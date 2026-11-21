(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed ENOMEM_in_mmap_errnos, M_loop, M_loop_fd1chan and 469 more; added ENOMEM_in_munmap_errnos, block_head_size_le, brk_grants_is_brk_zeros and 31 more; removed argv_layout_slack; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/MmapSim.v, 900 lines within its lines 11-1796. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From Stdlib Require FunctionalExtensionality. From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module CatExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_CatExec () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsCeq_rewrite_relationI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes;EquivalenceEpointwise_equivalenceC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:Proper_mapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsAms_read_bytes_auxK47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memK47Corelib4Init9Datatypes6option01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addK47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;memory_readC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<ms_read_byteK47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natc59OSSVerify5KrLib7Mh_00387CatExecEms_read_bytes_aux_rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC49OSSVerify5KrLib8PropExec6u_add1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05c59OSSVerify5KrLib7Mh_00387CatExec<wbytes_aboveC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c59OSSVerify5KrLib7Mh_00387CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00c59OSSVerify5KrLib7Mh_00387CatExec@rdn_wbytes_belowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExecCrdn_wbytes_disjointC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z6shiftrc59OSSVerify5KrLib7Mh_00387CatExecDlength_Z_to_le_bytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr07K47Corelib4Init9Datatypes4prod01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics5Riscv3Sem5is_x0C4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C49OSSVerify5KrLib8PropExec=bv_eqb0_is_x0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_gtK46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init9Datatypes4andbC49OSSVerify5KrLib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00c59OSSVerify5KrLib7Mh_00387CatExecBstack_max_size_valC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib7Mh_00387CatExec=flat_map_app'C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef5skipnC47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc59OSSVerify5KrLib7Mh_00387CatExec9skipn_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List<firstn_skipnC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc59OSSVerify5KrLib7Mh_00387CatExec>flat_map_splitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8word_le8C47Corelib4Init3Nat3addC49OSSVerify5KrLib8PropExecCtotal_arg_bytes_natC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00c59OSSVerify5KrLib7Mh_00387CatExecDtotal_arg_bytes_consC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6NArith6BinNat1N6of_natC56Stdlib6NArith6BinNat1N2leI47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib6ZArith4Znat7nat_N_ZC56Stdlib6ZArith4Znat3N2Z6inj_leK47Corelib4Init7Decimal4uint03K47Corelib4Init7Decimal4uint09K47Corelib4Init7Decimal4uint02K47Corelib4Init7Decimal4uint05K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintK47Corelib4Init7Decimal4uint01K47Corelib4Init7Decimal4uint04K47Corelib4Init7Decimal4uint07K47Corelib4Init7Decimal4uint0;C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<string_addrsC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC49OSSVerify5KrLib8PropExec:word_add_0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC35stdpp7tactics<f_equal_helpC49OSSVerify5KrLib8PropExecEnat_to_word_add_mergeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<len_word_natC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecJstring_addrs_fst_structureC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9word1_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExec?cat_string_baseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExec@nth_string_addrsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appc59OSSVerify5KrLib7Mh_00387CatExec<cat_env_baseC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout=at_random_ptrC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout:auxv_bytesC47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAlength_auxv_bytesC49OSSVerify5KrLib8PropExec@length_n_to_le_8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecGlength_string_addrs_fstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecClength_flat_map_le8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExecAcat_struct_prefixC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExec?cat_struct_sizeC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9auxv_sizeC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?flatten_stringsC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib5Lists7ListDef6repeatC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesI47Corelib4Init5Logic2ex00C49OSSVerify5KrLib8PropExecAstring_addrs_pairC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesc59OSSVerify5KrLib7Mh_00387CatExec?bsb_argv_prefixC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExecCflat_map_le8_decompC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List@firstn_length_lec59OSSVerify5KrLib7Mh_00387CatExec9bsb_ptr_kC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memC49OSSVerify5KrLib8PropExecDread_at_offset_imageC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExecAbsb_strings_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExecFflatten_strings_decompC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecFlength_flatten_stringsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExecHlength_cat_struct_prefixC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExec:bsb_byte_kC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecBread_byte_at_imageC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses:impl_morphc59OSSVerify5KrLib7Mh_00387CatExecCcat_argv_ptr_offsetC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8app_nth1c59OSSVerify5KrLib7Mh_00387CatExec7byte_atC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8app_nth2C47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC56Stdlib6ZArith4Znat5Nat2Z6inj_geK46Stdlib9micromega=RingMicromega3Op204C46Stdlib5Lists4List2InC46Stdlib5Lists4List6nth_Inc59OSSVerify5KrLib7Mh_00387CatExec>nth_lt_byte_atC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec>nth_app0_boundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenAopenat_plain_nameC47Corelib4Init9Datatypes3orbC47Corelib4Init9Datatypes4negbC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8dot_pathC49OSSVerify5KrLib8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsCbv_wrap_bv_unsignedC45stdpp9bitvector;definitionsCbv_wrap_add_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExec4pendC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprI59OSSVerify5KrLib7Mh_00306CatSim8to_wexit00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExec7adv_setC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim8to_wexit02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00307ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z4landC45stdpp9bitvector;definitions?bv_and_unsignedK59OSSVerify5KrLib7Mh_00306CatSim8to_wexit01C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9arg_reg_0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9arg_reg_2C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9arg_reg_1C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01c59OSSVerify5KrLib7Mh_00387CatExec8tw_exit0C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ms_read_bytes_aux_rdn : forall segs ms n addr,
  ms_rom ms = seg_rom segs ->
  ms_read_bytes_aux ms addr n = rdn segs (ms_mem ms) addr n.
Proof.
  intros segs ms n. induction n as [|n IH]; intros addr Hrom; [reflexivity|].
  cbn [ms_read_bytes_aux rdn]. unfold ms_read_byte. rewrite Hrom.
  destruct (ms_mem ms addr) as [b|].
  - rewrite IH by exact Hrom. reflexivity.
  - unfold seg_rom. destruct (memory_read segs addr 1) as [[|b r]|];
      try reflexivity; rewrite IH by exact Hrom; reflexivity.
Qed.

Lemma ms_read_bytes_rdn : forall segs ms addr len,
  ms_rom ms = seg_rom segs ->
  ms_read_bytes ms addr len = rdn segs (ms_mem ms) addr (word_to_nat len).
Proof. intros. unfold ms_read_bytes. apply ms_read_bytes_aux_rdn; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint wbytes (m : word -> option byte) (addr : word) (bs : list byte)
    : word -> option byte :=
  match bs with
  | [] => m
  | b :: rest => wbytes (fun a => if bv_eqb a addr then Some b else m a) (addr+1) rest
  end.

(* [comment removed for export] *)
Lemma wbytes_above : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m addr bs x = m x.
Proof.
  induction bs as [|b rest IH]; intros m addr x Hle; [reflexivity|].
  cbn [wbytes length] in *.
  pose proof (u64_range x) as Hx.
  assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
    by (apply u_add1; lia).
  rewrite IH by lia.
  cbv beta.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  rewrite Hne. reflexivity.
Qed.

Lemma rdn_wbytes_disjoint : forall segs bs m (addr a : word) n,
  (bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
  intros segs bs m addr a n Hle Hnw. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply wbytes_above. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_below : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned x < bv_unsigned addr)%Z ->
  wbytes m addr bs x = m x.
Proof.
  induction bs as [|b rest IH]; intros m addr x Hnw Hlt; [reflexivity|].
  cbn [wbytes length] in *.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  destruct rest as [|b' rest'].
  - cbn [wbytes]. rewrite Hne. reflexivity.
  - assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
      by (apply u_add1; cbn [length] in Hnw; lia).
    rewrite IH by lia.
    cbv beta. rewrite Hne. reflexivity.
Qed.

Lemma rdn_wbytes_below : forall segs bs m (addr a : word) n,
  (bv_unsigned a + Z.of_nat n <= bv_unsigned addr)%Z ->
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
  intros segs bs m addr a n Hle Hnw.
  pose proof (u64_range addr) as Ha.
  apply rdn_ext; [lia|].
  intros x Hx. apply wbytes_below; [exact Hnw|lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_wbytes_out : forall segs bs m (addr a : word) n,
  (bv_unsigned a + Z.of_nat n <= bv_unsigned addr
   \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
  intros segs bs m addr a n [Hb|Hd] Hnw Hnw'.
  - apply rdn_wbytes_below; [exact Hb | exact Hnw'].
  - apply rdn_wbytes_disjoint; [exact Hd | exact Hnw].
Qed.

Lemma length_Z_to_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes length]. rewrite IH. reflexivity.
Qed.

Lemma length_N_to_le_bytes : forall n (v : word), length (word_to_le_bytes n v) = n.
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

(* [comment removed for export] *)
Lemma write_to_mem_wbytes : forall bs (m : word -> option byte) (addr : word),
  write_to_mem m addr bs = wbytes m addr bs.
Proof.
  induction bs as [|b rest IH]; intros m addr; [reflexivity|].
  cbn [write_to_mem wbytes]. apply IH.
Qed.

(* [comment removed for export] *)
Lemma step_sd : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 8%nat = true ->
  exists bs, length bs = 8%nat /\
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) bs) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  exists (word_to_le_bytes 8 (getr regs rs2)). split; [reflexivity|].
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stack_max_size_val : stack_max_size = 8388608%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma launch_string_base_arith : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned sp
   + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp)
                 (in_envp inp))
   + Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                 (in_execfn inp))
   + 8 <= bv_unsigned (ed_top draw))%Z.
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  cbn [entry_launch_ok_va] in Hlaunch.
  destruct Hlaunch as (_ & (_ & _ & Hhi) & _).
  unfold launch_sp_hi, align_down16 in Hhi.
  pose proof (Z.mod_pos_bound
    (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                   (in_execfn inp))) 16 ltac:(lia)).
  lia.
Qed.

Lemma launch_sp_le_ed_top : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned sp <= bv_unsigned (ed_top draw))%Z.
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Nat2Z.is_nonneg
    (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  lia.
Qed.

Lemma wrap_mem_below :
  forall v inp mbase ph entry (sp brk : word) draw (addr : word),
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned addr < bv_unsigned sp - stack_max_size)%Z ->
  wrap_mem inp mbase ph entry sp draw addr = None.
Proof.
  intros v inp mbase ph entry sp brk draw addr Hlau Hlt.
  pose proof stack_max_size_val as Hsms.
  pose proof (launch_sp_le_ed_top v inp mbase sp brk draw Hlau) as Htop.
  pose proof (Z.le_max_l (bv_unsigned (ed_top draw) - stack_max_size)
                (bv_unsigned mbase + stack_guard_gap_bytes (in_kernel inp))) as Hmax.
  unfold wrap_mem, stack_to_mem.
  assert (Hsp : Z.leb (bv_unsigned sp) (bv_unsigned addr) = false)
    by (apply Z.leb_gt; lia).
  rewrite Hsp.
  assert (Hgate : Z.leb (stack_window_lo (in_kernel inp) mbase draw)
                        (bv_unsigned addr) = false)
    by (apply Z.leb_gt; unfold stack_window_lo in *; lia).
  rewrite Hgate. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma flat_map_app' : forall {A B : Type} (f : A -> list B) l1 l2,
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros A B f l1 l2. induction l1 as [|x xs IH]; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma skipn_nth : forall {A : Type} (l : list A) k d, (k < length l)%nat ->
  skipn k l = nth k l d :: skipn (S k) l.
Proof.
  induction l as [|x xs IH]; intros k d Hk; [cbn in Hk; lia|].
  destruct k as [|k']; [reflexivity|].
  cbn [skipn nth]. apply IH. cbn in Hk; lia.
Qed.

Lemma flat_map_split : forall {A B : Type} (f : A -> list B) l k d, (k < length l)%nat ->
  flat_map f l = flat_map f (firstn k l) ++ f (nth k l d) ++ flat_map f (skipn (S k) l).
Proof.
  intros A B f l k d Hk.
  rewrite <- (firstn_skipn k l) at 1.
  rewrite flat_map_app'.
  rewrite (skipn_nth l k d Hk). reflexivity.
Qed.

Lemma flat_map_le8_decomp : forall (l : list word) k, (k < length l)%nat ->
  flat_map word_le8 l =
  flat_map word_le8 (firstn k l) ++ word_le8 (nth k l (Z_to_bv 64 0))
    ++ flat_map word_le8 (skipn (S k) l).
Proof. intros l k Hk. apply (flat_map_split word_le8 l k (Z_to_bv 64 0) Hk). Qed.

Lemma flatten_strings_decomp : forall strs k, (k < length strs)%nat ->
  flatten_strings strs =
  flatten_strings (firstn k strs) ++ (nth k strs [] ++ [Z_to_bv 8 0])
    ++ flatten_strings (skipn (S k) strs).
Proof.
  intros strs k Hk.
  apply (flat_map_split (fun s => s ++ [Z_to_bv 8 0]) strs k [] Hk).
Qed.

Lemma total_arg_bytes_cons : forall s l,
  total_arg_bytes_nat (s :: l) = (length s + 1 + total_arg_bytes_nat l)%nat.
Proof. reflexivity. Qed.

Lemma total_arg_bytes_firstn_le : forall k l,
  (total_arg_bytes_nat (firstn k l) <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l.
  - change (total_arg_bytes_nat (firstn 0 l)) with 0%nat. lia.
  - destruct l as [|s rest]; [cbn; lia|].
    cbn [firstn]. rewrite !total_arg_bytes_cons. specialize (IH rest). lia.
Qed.

(* Ported by name from 727298f3:theories/Common/CatExec.v.  String [k], its
   bytes and its NUL all fit inside the blob: what bounds an argv pointer now
   that the strings sit at the TOP of the block ([argv_ptr_bounds] below). *)
Lemma total_arg_bytes_firstn_within : forall (l : list (list byte)) k,
  (k < length l)%nat ->
  (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1
   <= total_arg_bytes_nat l)%nat.
Proof.
  intros l. induction l as [|s rest IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k'].
  - cbn [firstn nth]. change (total_arg_bytes_nat []) with 0%nat.
    rewrite total_arg_bytes_cons. lia.
  - cbn [firstn nth]. rewrite !total_arg_bytes_cons.
    specialize (IH k' ltac:(cbn in Hk; lia)). lia.
Qed.

Lemma natN_le : forall n m, (n <= m)%nat -> (N.of_nat n <= N.of_nat m)%N.
Proof. intros n m H. lia. Qed.

(* [comment removed for export] *)
Lemma of_nat_131071 : Z.of_nat 131071 = 131071%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma of_nat_2097152 : Z.of_nat 2097152 = 2097152%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cat_struct_size (av ev : list (list byte)) : nat :=
  (8 * block_items av ev)%nat.

Definition cat_string_base (top : word) (av ev : list (list byte))
    (execfn : list byte) : word :=
  string_base_addr top av ev execfn.

Definition cat_env_base (top : word) (av ev : list (list byte))
    (execfn : list byte) : word :=
  cat_string_base top av ev execfn + nat_to_word (total_arg_bytes_nat av).

(* [comment removed for export] *)
Definition cat_argv_ptr (top : word) (av ev : list (list byte))
    (execfn : list byte) (k : nat) : word :=
  nth k (fst (string_addrs (cat_string_base top av ev execfn) av)) (Z_to_bv 64 0).

Lemma nth_string_addrs : forall strs (base : word) k, (k < length strs)%nat ->
  nth k (fst (string_addrs base strs)) (Z_to_bv 64 0)
  = base + nat_to_word (total_arg_bytes_nat (firstn k strs)).
Proof.
  induction strs as [|s rest IH]; intros base k Hk; [cbn in Hk; lia|].
  rewrite string_addrs_fst_structure.
  destruct k as [|k'].
  - cbn [nth firstn]. change (total_arg_bytes_nat []) with 0%nat.
    rewrite word_add_0. reflexivity.
  - cbn [nth]. rewrite (IH (base + len_word s + 1) k' ltac:(cbn in Hk; lia)).
    cbn [firstn]. rewrite total_arg_bytes_cons.
    rewrite len_word_nat, word1_nat, !nat_to_word_add_merge.
    f_equal. f_equal. lia.
Qed.

Lemma cat_argv_ptr_offset : forall top av ev execfn k, (k < length av)%nat ->
  cat_argv_ptr top av ev execfn k
  = cat_string_base top av ev execfn
    + nat_to_word (total_arg_bytes_nat (firstn k av)).
Proof. intros. unfold cat_argv_ptr. apply nth_string_addrs. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cat_struct_prefix (top : word) (av ev : list (list byte))
    (execfn : list byte) : list byte :=
  word_le8 (len_word av)
  ++ flat_map word_le8 (fst (string_addrs (cat_string_base top av ev execfn) av))
  ++ word_le8 (Z_to_bv 64 0)
  ++ flat_map word_le8 (fst (string_addrs (cat_env_base top av ev execfn) ev))
  ++ word_le8 (Z_to_bv 64 0).

Lemma length_cat_struct_prefix : forall top av ev execfn,
  length (cat_struct_prefix top av ev execfn) = cat_struct_size av ev.
Proof.
  intros top av ev execfn.
  unfold cat_struct_prefix, cat_struct_size, block_items.
  rewrite !length_app, !length_flat_map_le8, !length_string_addrs_fst,
    !length_n_to_le_8.
  lia.
Qed.

(* [comment removed for export] *)
Lemma bsb_argv_prefix : forall inp mbase ph entry (sp : word) draw, exists tail,
  entry_stack_image inp mbase ph entry sp draw =
    word_le8 (len_word (in_argv inp))
    ++ flat_map word_le8
         (fst (string_addrs
                 (cat_string_base (ed_top draw) (in_argv inp) (in_envp inp)
                    (in_execfn inp))
                 (in_argv inp)))
    ++ tail.
Proof.
  intros inp mbase ph entry sp draw.
  rewrite entry_stack_image_block.
  unfold build_stack_bytes, cat_string_base. cbv zeta.
  rewrite (string_addrs_pair (in_argv inp)). cbv beta iota.
  rewrite (string_addrs_pair (in_envp inp)). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bsb_ptr_k : forall inp mbase ph entry (sp : word) draw k,
  (k < length (in_argv inp))%nat -> exists post,
  entry_stack_image inp mbase ph entry sp draw =
    (word_le8 (len_word (in_argv inp))
      ++ flat_map word_le8
           (firstn k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp)))))
    ++ word_le8 (nth k (fst (string_addrs
                               (cat_string_base (ed_top draw) (in_argv inp)
                                  (in_envp inp) (in_execfn inp))
                               (in_argv inp))) (Z_to_bv 64 0))
    ++ post.
Proof.
  intros inp mbase ph entry sp draw k Hk.
  destruct (bsb_argv_prefix inp mbase ph entry sp draw) as [tail E].
  assert (Hk' : (k < length (fst (string_addrs
                   (cat_string_base (ed_top draw) (in_argv inp) (in_envp inp)
                      (in_execfn inp)) (in_argv inp))))%nat)
    by (rewrite length_string_addrs_fst; exact Hk).
  rewrite (flat_map_le8_decomp _ k Hk') in E.
  eexists. rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma read_argv_ptr_k : forall segs inp mbase ph entry (sp : word) draw k,
  (k < length (in_argv inp))%nat ->
  (bv_unsigned sp
   + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
     < 2 ^ 64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (sp + nat_to_word (8 + 8 * k)) 8%nat
  = Some (word_le8 (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                      (in_execfn inp) k)).
Proof.
  intros segs inp mbase ph entry sp draw k Hk Hnw.
  destruct (bsb_ptr_k inp mbase ph entry sp draw k Hk) as [post E].
  pose proof (read_at_offset_image segs inp mbase ph entry sp draw
    (word_le8 (len_word (in_argv inp))
      ++ flat_map word_le8
           (firstn k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp)))))
    (word_le8 (nth k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp))) (Z_to_bv 64 0)))
    post 8%nat E (length_n_to_le_8 _) Hnw) as H'.
  assert (Hlen : length (word_le8 (len_word (in_argv inp))
      ++ flat_map word_le8
           (firstn k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp)))))
    = (8 + 8 * k)%nat).
  { rewrite length_app, length_n_to_le_8, length_flat_map_le8, firstn_length_le;
      [reflexivity | rewrite length_string_addrs_fst; lia]. }
  rewrite Hlen in H'.
  rewrite H'. unfold cat_argv_ptr. reflexivity.
Qed.

(* [comment removed for export] *)
Definition cat_block_head (la : LaunchAuxv) (ph : PhdrInfo)
    (entry sp top : word) (av ev : list (list byte)) (execfn : list byte)
    (uid gid hw : word) (draw : EntryDraw) : list byte :=
  block_below_random la ph entry sp top av ev execfn uid gid hw
  ++ at_random_bytes (ed_random draw)
  ++ repeat (Z_to_bv 8 0) (block_pad_len (la_rseq la) sp top av ev execfn).

Lemma bsb_strings_split : forall inp mbase ph entry (sp : word) draw, exists tail,
  entry_stack_image inp mbase ph entry sp draw
  = cat_block_head (launch_auxv inp sp mbase) ph entry sp (ed_top draw)
      (in_argv inp) (in_envp inp) (in_execfn inp)
      (in_uid inp) (in_gid inp) (in_hwcap inp) draw
    ++ flatten_strings (in_argv inp) ++ tail.
Proof.
  intros inp mbase ph entry sp draw.
  rewrite entry_stack_image_block, build_stack_bytes_split_random.
  unfold cat_block_head, block_above_random.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

Definition cat_string_off (rseq : bool) (sp top : word)
    (av ev : list (list byte)) (execfn : list byte) : nat :=
  (block_head_size rseq av ev + block_pad_len rseq sp top av ev execfn)%nat.

Lemma length_cat_block_head :
  forall la ph entry sp top av ev execfn uid gid hw draw,
  length (cat_block_head la ph entry sp top av ev execfn uid gid hw draw)
  = cat_string_off (la_rseq la) sp top av ev execfn.
Proof.
  intros la ph entry sp top av ev execfn uid gid hw draw.
  unfold cat_block_head, block_below_random, cat_string_off. cbv zeta.
  rewrite (string_addrs_pair av). cbv beta iota.
  rewrite (string_addrs_pair ev). cbv beta iota.
  rewrite !length_app, !repeat_length, !length_flat_map_le8,
    !length_string_addrs_fst, length_auxv_bytes, length_at_random_bytes,
    !length_n_to_le_8.
  unfold block_head_size, block_items. lia.
Qed.

Lemma bsb_byte_k : forall inp mbase ph entry (sp : word) draw k,
  (k < length (in_argv inp))%nat -> exists pre post,
  entry_stack_image inp mbase ph entry sp draw
  = pre ++ (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) ++ post
  /\ length pre
     = (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
          (in_argv inp) (in_envp inp) (in_execfn inp)
        + total_arg_bytes_nat (firstn k (in_argv inp)))%nat.
Proof.
  intros inp mbase ph entry sp draw k Hk.
  destruct (bsb_strings_split inp mbase ph entry sp draw) as [tail E].
  rewrite (flatten_strings_decomp (in_argv inp) k Hk) in E.
  exists (cat_block_head (launch_auxv inp sp mbase) ph entry sp (ed_top draw)
            (in_argv inp) (in_envp inp) (in_execfn inp)
            (in_uid inp) (in_gid inp) (in_hwcap inp) draw
          ++ flatten_strings (firstn k (in_argv inp))).
  eexists.
  split.
  - rewrite E. rewrite <- !app_assoc. reflexivity.
  - rewrite length_app, length_cat_block_head, length_flatten_strings.
    reflexivity.
Qed.

Lemma u_Z2bv_lt : forall z, (0 <= z)%Z -> (z < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z H0 H1. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  apply Z.mod_small. lia.
Qed.

Lemma word_add_nat_Z2bv : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zplus_mod_idemp_r.
Qed.

Lemma word_sub_nat : forall (a : word) (n : nat),
  a - nat_to_word n = Z_to_bv 64 (bv_unsigned a - Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_sub_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zminus_mod_idemp_r.
Qed.

Lemma u_cat_string_base : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  bv_unsigned (cat_string_base (ed_top draw) (in_argv inp) (in_envp inp)
                 (in_execfn inp))
  = (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                   (in_execfn inp)))%Z.
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch) as HA.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  unfold cat_string_base, string_base_addr. rewrite word_sub_nat.
  assert (Hz : (0 <= bv_unsigned (ed_top draw)
                     - Z.of_nat (8 + launch_string_bytes (in_argv inp)
                                       (in_envp inp) (in_execfn inp))
                < 2 ^ 64)%Z).
  { rewrite Nat2Z.inj_add. change (Z.of_nat 8) with 8%Z. lia. }
  rewrite (u_Z2bv_lt _ (proj1 Hz) (proj2 Hz)).
  rewrite Nat2Z.inj_add. change (Z.of_nat 8) with 8%Z. lia.
Qed.

Lemma cat_string_base_offset : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  cat_string_base (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp)
  = sp + nat_to_word (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                        (in_argv inp) (in_envp inp) (in_execfn inp)).
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch) as HA.
  pose proof (u_cat_string_base v inp mbase sp brk draw Hlaunch) as Hu.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  apply bv_eq. rewrite Hu, word_add_nat_Z2bv.
  unfold cat_string_off, block_pad_len.
  rewrite u_Z2bv_lt
    by (rewrite Nat2Z.inj_add; rewrite Z2Nat.id by lia; lia).
  rewrite Nat2Z.inj_add. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma read_argv_byte_k :
  forall v segs inp mbase ph entry (sp brk : word) draw k j,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  (j <= length (nth k (in_argv inp) []))%nat ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k
       + nat_to_word j) 1%nat
  = Some [nth j (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)].
Proof.
  intros v segs inp mbase ph entry sp brk draw k j Hlaunch Hk Hj.
  pose proof (entry_stack_image_no_wrap v inp mbase ph entry sp brk draw Hlaunch)
    as Hnw.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk) as [pre [post [E Hlen]]].
  pose proof (read_byte_at_image segs inp mbase ph entry sp draw
    pre (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) post j E) as H'.
  rewrite Hlen in H'.
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
             (in_execfn inp) k + nat_to_word j)
    with (sp + nat_to_word
                 (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                    (in_argv inp) (in_envp inp) (in_execfn inp)
                  + total_arg_bytes_nat (firstn k (in_argv inp)) + j)).
  2:{ rewrite (cat_argv_ptr_offset _ _ _ _ k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlaunch).
      rewrite !nat_to_word_add_merge. f_equal. f_equal. lia. }
  apply H'; [rewrite length_app; cbn [length]; lia | exact Hnw].
Qed.

Lemma read_argv_str_k :
  forall v segs inp mbase ph entry (sp brk : word) draw k,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
      (length (nth k (in_argv inp) []))
  = Some (nth k (in_argv inp) []).
Proof.
  intros v segs inp mbase ph entry sp brk draw k Hlaunch Hk.
  pose proof (entry_stack_image_no_wrap v inp mbase ph entry sp brk draw Hlaunch)
    as Hnw.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs inp mbase ph entry sp draw
    pre (nth k (in_argv inp) []) ([Z_to_bv 8 0] ++ post)
    (length (nth k (in_argv inp) []))) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
             (in_execfn inp) k)
    with (sp + nat_to_word
                 (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                    (in_argv inp) (in_envp inp) (in_execfn inp)
                  + total_arg_bytes_nat (firstn k (in_argv inp)))).
  2:{ rewrite (cat_argv_ptr_offset _ _ _ _ k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlaunch).
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [ | reflexivity | exact Hnw].
  rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition byte_at (s : list byte) (k : nat) : byte :=
  nth k (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).

Lemma nth_lt_byte_at : forall s j, (j < length s)%nat ->
  byte_at s j = nth j s (Z_to_bv 8 0).
Proof. intros s j Hj. unfold byte_at. apply app_nth1. exact Hj. Qed.

Lemma byte_at_len : forall s, byte_at s (length s) = Z_to_bv 8 0.
Proof.
  intros s. unfold byte_at. rewrite app_nth2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma byte_at_nz : forall s j, ~ In (Z_to_bv 8 0) s -> (j < length s)%nat ->
  byte_at s j <> Z_to_bv 8 0.
Proof.
  intros s j Hnz Hj Hc.
  apply Hnz. rewrite <- Hc. rewrite nth_lt_byte_at by exact Hj.
  apply nth_In. exact Hj.
Qed.

(* [comment removed for export] *)
Lemma byte_at_bound : forall s j, (bv_unsigned (byte_at s j) < 256)%Z.
Proof. intros s j. unfold byte_at. apply nth_app0_bound. Qed.

Lemma valid_argv_len : forall av, valid_argv av ->
  (Z.of_nat (length av) <= 1024)%Z.
Proof. intros av [Hlen _]. lia. Qed.

Lemma valid_argv_nonempty : forall av, valid_argv av -> (1 <= length av)%nat.
Proof. intros av [Hlen _]. lia. Qed.

Lemma valid_argv_str_len : forall av k, valid_argv av -> (k < length av)%nat ->
  (Z.of_nat (length (nth k av [])) <= 131071)%Z.
Proof.
  intros av k [_ [_ [Hstr _]]] Hk.
  rewrite Forall_forall in Hstr.
  specialize (Hstr _ (nth_In av [] Hk)). exact Hstr.
Qed.

Lemma valid_argv_str_nz : forall av k, valid_argv av -> (k < length av)%nat ->
  ~ In (Z_to_bv 8 0) (nth k av []).
Proof.
  intros av k [_ [_ [_ [Hnz _]]]] Hk.
  rewrite Forall_forall in Hnz. apply Hnz. apply nth_In. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma valid_argv_str_plain : forall av k, valid_argv av ->
  (S k < length av)%nat ->
  path_eqb (nth (S k) av []) dot_path = false ->
  openat_plain_name (nth (S k) av []) = true.
Proof.
  intros av k [_ [_ [_ [_ Hpl]]]] Hk Hdot.
  assert (Hnth : nth (S k) av [] = nth k (tl av) []).
  { destruct av as [|a av']; [cbn in Hk; lia | reflexivity]. }
  assert (Hk' : (k < length (tl av))%nat).
  { destruct av as [|a av']; cbn in *; lia. }
  rewrite Forall_forall in Hpl.
  destruct (Hpl _ (nth_In (tl av) [] Hk')) as [Hsl Hdd].
  rewrite Hnth in Hdot |- *.
  unfold openat_plain_name, path_is_dirref.
  rewrite Hdot, Hsl, Hdd. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma valid_argv_str_bytes : forall av k, valid_argv av -> (k < length av)%nat ->
  Forall (fun b : byte => (bv_unsigned b < 256)%Z) (nth k av []).
Proof.
  intros av k _ _. apply Forall_forall. intros b _. apply u8_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_addi_pred : forall x : word, v_addi (x + 1) (-1) = x.
Proof.
  intro x. apply bv_eq. unfold v_addi.
  rewrite Z_to_bv_unsigned, bv_add_unsigned.
  change (bv_unsigned (1 : word)) with 1%Z.
  rewrite bv_wrap_add_idemp_l.
  replace (bv_unsigned x + 1 + -1)%Z with (bv_unsigned x) by lia.
  apply bv_wrap_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (Z_to_bv 64 64);
     ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.

(* [comment removed for export] *)
Lemma adv_set : forall regs pc sv mem rom v,
  advance_past_svc (set_gpr0
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |} v)
  = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof.
  intros regs pc sv mem rom v.
  unfold advance_past_svc, set_gpr0, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tw_write_gen : forall segs regs pc mem rom buf bufs code,
  ms_gpr (pend regs pc mem rom) 0 = Z_to_bv 64 1 ->
  ms_read_bytes (pend regs pc mem rom)
    (ms_gpr (pend regs pc mem rom) 1) (ms_gpr (pend regs pc mem rom) 2) = Some buf ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb (ms_gpr (pend regs pc mem rom) 1)
    (bv_unsigned (ms_gpr (pend regs pc mem rom) 2)) = true ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     to_wexit segs (mkst (regupd regs 10 (len_word (firstn n buf)))
                         (v_addi pc 4) mem rom) bufs code) ->
  to_wexit segs (pend regs pc mem rom) (buf :: bufs) code.
Proof.
  intros segs regs pc mem rom buf bufs code Hg0 Hr Hok Hnb Hcont.
  eapply tw_write;
    [reflexivity | reflexivity | exact Hg0 | exact Hr | exact Hok | exact Hnb | ].
  intros n Hn1 Hn2. unfold pend. rewrite adv_set. apply Hcont; assumption.
Qed.

(* [comment removed for export] *)
Lemma tw_exit0 : forall segs ms x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
  ms_gpr ms 0 = Z_to_bv 64 0 ->
  to_wexit segs ms [] (Z_to_bv 64 0).
Proof.
  intros segs ms x8 Hsvc Hex Hg0.
  assert (Hc : bv_and (ms_gpr ms 0) (Z_to_bv 64 255) = Z_to_bv 64 0).
  { rewrite Hg0. apply bv_eq.
    rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity. }
  rewrite <- Hc. eapply tw_exit; eassumption.
Qed.

(* [comment removed for export] *)
Lemma tw_write_rec : forall segs regs pc mem rom buf bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some buf ->
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     to_wexit segs (mkst (regupd regs 10 (len_word (firstn n buf)))
                         (v_addi pc 4) mem rom) bufs code) ->
  to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (buf :: bufs) code.
Proof.
  intros segs regs pc mem rom buf bufs code H17 H10 Hr Hok Hnb Hcont.
  eapply tw_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. apply Hcont; assumption.
Qed.

(* [comment removed for export] *)
Lemma tw_exit_rec : forall segs regs pc mem rom,
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = Z_to_bv 64 0 ->
  to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |} [] (Z_to_bv 64 0).
Proof.
  intros segs regs pc mem rom H17 H10.
  eapply tw_exit0.
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
  - unfold ms_gpr. cbn [ms_regs].
    rewrite arg_reg_0. exact H10.
Qed.
End WithFP.

End CatExec.
Module SeqExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_SeqExec () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsCeq_rewrite_relationI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes;EquivalenceEpointwise_equivalenceC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:Proper_mapc59OSSVerify5KrLib7Mh_00387CatExec=flat_map_app'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00387CatExec9skipn_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_00387CatExec>flat_map_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr03K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics5Riscv3Sem5is_x0C49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK47Corelib4Init5Logic2eq01C49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec=bv_eqb0_is_x0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5instr04C49OSSVerify5KrLib8PropExec=step_jalr_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memc59OSSVerify5KrLib7Mh_00387CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib7Mh_00387SeqExec;step_sd_valC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C49OSSVerify5KrLib8PropExec9step_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0:C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_subC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5instr01C56Stdlib6ZArith6BinInt1Z6shiftlC49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C49OSSVerify5KrLib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:step_auipcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C49OSSVerify5KrLib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:step_addiwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:step_sltiuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05C49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_xoriC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5instr0BC49OSSVerify5KrLib8PropExec5v_mulC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_mulC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01C49OSSVerify5KrLib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_andiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:C49OSSVerify5KrLib8PropExec5v_oriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_oriC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5instr09C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_slliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03C49OSSVerify5KrLib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_srliC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07C49OSSVerify5KrLib8PropExec6v_sraiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_sraiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop08C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC49OSSVerify5KrLib8PropExec6u_add1C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c59OSSVerify5KrLib7Mh_00387CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib7Mh_00387SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC49OSSVerify5KrLib8PropExec:bytes_le_NC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions=bv_wrap_smallK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions>bv_swrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedK46Stdlib9micromega5Tauto8GFormula05C45stdpp9bitvector;definitions5bv_eqc59OSSVerify5KrLib7Mh_00387SeqExec=v_addiw_smallC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC45stdpp9bitvector;definitions?bv_and_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesI47Corelib4Init5Peano2le00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordI59OSSVerify5KrLib7Mh_00306CatSim8to_wexit00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcc59OSSVerify5KrLib7Mh_00387CatExec7adv_setC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim8to_wexit02C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9arg_reg_0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9arg_reg_2C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9arg_reg_1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387SeqExec>land_255_smallC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K59OSSVerify5KrLib7Mh_00306CatSim8to_wexit01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC47Corelib4Init5Peano2ltc59OSSVerify5KrLib7Mh_00387CatExec>valid_argv_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExecBvalid_argv_str_lenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlc59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecCtotal_arg_bytes_natC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecAtotal_arg_bytes_ZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExecItotal_arg_bytes_firstn_leC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib4Init3Nat3mulc59OSSVerify5KrLib7Mh_00387SeqExecAargv_struct_arithC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z7inj_mulc59OSSVerify5KrLib7Mh_00387CatExec?cat_struct_sizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExec?cat_string_baseC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC49OSSVerify5KrLib8PropExecEnat_to_word_add_mergeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExecCcat_argv_ptr_offsetC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387SeqExec>argv_sum_arithC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c59OSSVerify5KrLib7Mh_00387SeqExec>argv_mod_arithC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCbv_wrap_add_idemp_rC45stdpp9bitvector;definitions?bv_add_unsignedc59OSSVerify5KrLib7Mh_00387SeqExec@argv_final_arithC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltc59OSSVerify5KrLib7Mh_00387SeqExecAargv_layout_slackC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathc59OSSVerify5KrLib7Mh_00387SeqExec6v_jalrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387SeqExec9step_jalrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_divuc59OSSVerify5KrLib7Mh_00387SeqExec6v_divuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z;le_lt_transK47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_symC45stdpp9bitvector;definitions@bv_divu_unsignedC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic5proj2K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega5Psatz05I47Corelib4Init5Logic5False00C45stdpp9bitvector;definitions7bv_moduc59OSSVerify5KrLib7Mh_00387SeqExec6v_remuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula03C45stdpp9bitvector;definitions@bv_modu_unsignedC4ELinuxProcessSemantics5Riscv3Sem7mul_divc59OSSVerify5KrLib7Mh_00387SeqExec6m_divuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<step_mul_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop06c59OSSVerify5KrLib7Mh_00387SeqExec6m_remuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop08K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC49OSSVerify5KrLib8PropExec6ov_rdnC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03K47Corelib7Numbers7BinNums1N01C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6NArith6BinNat1N2leC45stdpp9bitvector;definitions?bv_wrap_bv_wrapC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitionsCbv_extract_unsignedC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith4Znat3N2Z6inj_leK4ELinuxProcessSemantics5Riscv5Instr5msize01c59OSSVerify5KrLib7Mh_00387SeqExec7step_sbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z;shiftr_specK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC56Stdlib6ZArith6BinInt1ZBmod_pow2_bits_highC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith4Znat3N2Z9is_nonnegC56Stdlib6NArith6BinNat1N3subC56Stdlib6ZArith6BinInt1Z8max_specc59OSSVerify5KrLib7Mh_00387SeqExec>Zmod_pow2_div8C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith4Znat3N2Z;inj_sub_maxc59OSSVerify5KrLib7Mh_00387SeqExecBZ_to_le_bytes_wrapC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32c59OSSVerify5KrLib7Mh_00387SeqExecAstore_bytes_low32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387SeqExec;step_sw_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387SeqExecAstore_bytes_low16C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize02c59OSSVerify5KrLib7Mh_00387SeqExec;step_sh_valC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_subwC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z?shiftl_spec_lowC49OSSVerify5KrLib8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z4lxorc59OSSVerify5KrLib7Mh_00387SeqExec8land_d48C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorc59OSSVerify5KrLib7Mh_00387SeqExec=lor_small_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:word_add_0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec9word1_natC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_sym".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition v_jalr (x : word) (imm : Z) : word := Z_to_bv 64 (jalr_tgtZ x imm).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_jal_link : forall segs regs pc mem rom w rd (imm : bv 21),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                  (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_addsext;
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_jalr : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                  (v_jalr (getr regs rs1) (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hf He Hd.
  exact (step_jalr_gen segs regs pc mem rom w rd rs1 imm Hf He Hd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_sd_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 8 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sd_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 v)) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sd_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)
Lemma step_addi_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_addi segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_add_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_add (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_add segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_sub_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_sub (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_sub segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_lui_at : forall segs regs pc mem rom w rd (imm : bv 20) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_lui (Z.shiftl (bv_signed imm) 12) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv.
  rewrite (step_lui segs regs pc mem rom w rd imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_auipc_at : forall segs regs pc mem rom w rd (imm : bv 20) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_auipc pc (Z.shiftl (bv_signed imm) 12) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv.
  rewrite (step_auipc segs regs pc mem rom w rd imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_addiw_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addiw (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_addiw segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_sltiu_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_SLTU rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_sltiu (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_sltiu segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_xori_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_XOR rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_xori (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_xori segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_mul_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MUL rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_mul (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mul segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_andi_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_andi (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_andi segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_ori_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_OR rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_ori (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_ori segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_slli_at : forall segs regs pc mem rom w rd rs (sh : bv 6) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_slli (getr regs rs) (bv_unsigned sh) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
  rewrite (step_slli segs regs pc mem rom w rd rs sh Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_srli_at : forall segs regs pc mem rom w rd rs (sh : bv 6) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_srli (getr regs rs) (bv_unsigned sh) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
  rewrite (PropExec.step_srli segs regs pc mem rom w rd rs sh Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_srai_at : forall segs regs pc mem rom w rd rs (sh : bv 6) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SRA rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_srai (getr regs rs) (bv_unsigned sh) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
  rewrite (step_srai segs regs pc mem rom w rd rs sh Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rdn_wbytes_hit : forall segs bs m (a : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m a bs) a (length bs) = Some bs.
Proof.
  intros segs bs. induction bs as [|b rest IH]; intros m a Hnw; [reflexivity|].
  cbn [length] in Hnw |- *.
  change (wbytes m a (b :: rest))
    with (wbytes (fun x => if bv_eqb x a then Some b else m x) (a+1) rest).
  set (m' := fun x : word => if bv_eqb x a then Some b else m x).
  cbn [rdn].
  destruct rest as [|b' rest'].
  - cbn [wbytes rdn]. unfold m'. rewrite bv_eqb_refl. reflexivity.
  - assert (Hu1 : bv_unsigned (a+1) = (bv_unsigned a + 1)%Z)
      by (apply u_add1; cbn [length] in Hnw; lia).
    assert (Hread : wbytes m' (a+1) (b' :: rest') a = Some b).
    { rewrite (wbytes_below (b' :: rest') m' (a+1) a);
        [ unfold m'; rewrite bv_eqb_refl; reflexivity
        | cbn [length] in *; lia
        | pose proof (u64_range a); lia ]. }
    rewrite Hread.
    rewrite (IH m' (a+1)) by (cbn [length] in *; lia).
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_wbytes_hit8 : forall segs m (a v : word),
  (bv_unsigned a + 8 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 8 v)) a 8%nat = Some (word_to_le_bytes 8 v).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 8 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

(* [comment removed for export] *)
Lemma bytes_le_to_Z_8 : forall v : word,
  bytes_le_to_Z (word_to_le_bytes 8 v) = bv_unsigned v.
Proof.
  intro v. rewrite bytes_le_N.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z.
  apply Z.mod_small. apply u64_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma c_ltu_ltb : forall x y : word,
  c_ltu x y = (bv_unsigned x <? bv_unsigned y)%Z.
Proof. reflexivity. Qed.

Lemma v_addiw_small : forall (x : word) imm,
  (0 <= bv_unsigned x + imm)%Z -> (bv_unsigned x + imm < 2^31)%Z -> (0 <= imm)%Z ->
  bv_unsigned (v_addiw x imm) = (bv_unsigned x + imm)%Z.
Proof.
  intros x imm Hlo Hhi _. unfold v_addiw.
  rewrite Z_to_bv_unsigned.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma v_addiw_id : forall x : word, (bv_unsigned x < 2^31)%Z -> v_addiw x 0 = x.
Proof.
  intros x Hx. apply bv_eq.
  rewrite (v_addiw_small x 0); [lia | pose proof (u64_range x); lia .. ].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_255_small : forall c : word, (bv_unsigned c < 256)%Z ->
  bv_and c (Z_to_bv 64 255) = c.
Proof.
  intros c Hc. apply bv_eq.
  rewrite bv_and_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 255) with (Z.ones 8).
  rewrite Z.land_ones by lia.
  apply Z.mod_small.
  pose proof (u64_range c). change (2^8)%Z with 256%Z. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tw_write_ret : forall segs regs pc mem rom buf bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some buf ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     to_wexit segs (mkst (regupd regs 10 (len_word (firstn n buf)))
                         (v_addi pc 4) mem rom) bufs code) ->
  to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (buf :: bufs) code.
Proof.
  intros segs regs pc mem rom buf bufs code H17 H10 Hr Hok Hnb Hcont.
  eapply tw_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. apply Hcont; assumption.
Qed.

(* [comment removed for export] *)
Lemma tw_exit_coden : forall segs regs pc mem rom (c : word),
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = c -> (bv_unsigned c < 256)%Z ->
  to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |} [] c.
Proof.
  intros segs regs pc mem rom c H17 H10 Hc.
  assert (Hg : bv_and (ms_gpr {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                                 ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                                 ms_mem := mem; ms_rom := rom |} 0)
                      (Z_to_bv 64 255) = c).
  { unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0, H10.
    apply land_255_small. exact Hc. }
  rewrite <- Hg.
  eapply tw_exit.
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Local Lemma argv_struct_arith : forall a e : Z,
  (0 <= a)%Z -> (a <= 1024)%Z -> (0 <= e)%Z -> (e <= 256)%Z ->
  (8 + (a + 1) * 8 + (e + 1) * 8 + 160 <= 10424)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SeqExec ()) ["WithFP1"] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61ah71ep;2p;1p;3p;4p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p6051001RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p60521000R=P9p8P=P5p8P=P0p8P=P@p8p100EEp6051000R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp6051001REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp60521000RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8p100H`p4p7210R@P7p8P@P:p8P@P;p8P@P5p8P@p100ILp4p710p8P@p100Iip4p710p8P@p100K0p4p710p8p100L:p4p710P5p8p100LUp4p70R@P1p8P@P2p8P@P7p8P@P:p8P@P;p8P@P4p8P@P3p8P@P<p8P@P5p8P@P6p8P>P5p8PEP7p8PEP5p8g02>fj20Tg00Mkj12Tg00USj14Tg02C7j2;Tg01LVj1:Tg02C`j3=Tg02DIj2GTg039mj2FTg00]ej1ETg01TUj3DTg00MKj1BTg02E5j2ATg02ESj1UTg02F1j4TTg02FOj1STg02Fmj1NTg02H;j2>Tg012gj1MTg02T9j35Tg03:Yj3<Tg00NPj16Tg02Ilj2HTg01:lj2ITg02JNj2JTg00R<j3KTg02K:j3LTg02KYj4CTg02>Ij27Tg02^<j2@Tg02GXj2OTg02IAj4PTg02SUj7QTg02T\j8RTf0R5#2#2p=1g01G4RE/O5p=3PEf1R7g02UdP5CPp=9P7g02VKR>g02VjR6P6g02WJR@P5g02WjFQp=8f3R<P>P6P6P@f2R>P7P5GRp=?g01HWR3/07g01DcR4#2R;#1R:#2#1#1R2#1#4R1,0>103>%42R2,0<g02YJRBg01V`R0,;ER=%:0#:R0#:,;E1;E05=E9=E=g02Z6'G'F%EB3D%BBPE1AE>P7%UECT%SE%NERB1>E;R=%32'9,8B%M6R6PB1>E4R0%31'9,8BP6%4:R:#3R6%44R4#3R?95E0=<E655EA5E=?=<E655E%6;#2#1R;#1#4R6#355E%6;#2#6#6#6#2#1#4R;#3'9,8BC?C?1HB@P5P>g01EHRBg01U5R@'I1J5>=KB@dALE37CCb3b4b5X0EX1E1072107117>4/@:,7:17<4/@:'7/76/0;[[^0E^1EP5f5f6P7P<O4b2UUUUX7EX6Eo"). Qed.

Local Lemma argv_sum_arith : forall a b : Z,
  (a <= 10424)%Z -> (b <= 2097152)%Z -> (a + b <= 2107576)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SeqExec ()) ["WithFP1"] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61ah71bp;1p;2p;3p;4p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p6051001RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p60521000R=P9p8P=P5p8P=P0p8P=P@p8p100EEp6051000R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp6051001REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp60521000RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8p100H`p4p7210R@P7p8P@P:p8P@P;p8P@P5p8P@p100ILp4p710p8P@p100Iip4p710p8P@p100K0p4p710p8p100L:p4p710P5p8p100LUp4p70R@P1p8P@P2p8P@P7p8P@P:p8P@P;p8P@P4p8P@P3p8P@P<p8P@P5p8P@P6p8P>P5p8PEP7p8PEP5p8g00Mkj10Tg00NPj11Tg00USj18Tg02>fj29Tg01LVj1;Tg02C7j24Tg02C`j3=Tg02DIj2BTg00]ej1ATg01TUj3?Tg00MKj1>Tg02E5j2RTg02ESj1QTg02F1j4PTg02FOj1LTg02Fmj1KTg02H;j2:Tg02GXj25Tg012gj1ETg02T9j3DTg02Ilj2CTg01:lj2FTg02JNj2GTg00R<j3HTg02K:j3ITg02KYj4JTg02>Ij2@Tg02IAj4MTg02SUj7NTg02T\j8OTf0R5#0#0p=2%05#0#0#0p=3g01G4REf1R7g02UdP5CMp=7P7g02VKR>g02VjR6P6g02WJR@P5g02WjFNp=6f3R<P>P6P6P@f2R>P7P5GOp=<g01DcR3#0R4#1#0#2#1#0#1#1#1#0#2#8R;,97R:%24#3R2#2#3#3#3#8R1,97RBg02YJR0g01V`R=#;R?#;,4E14E?14E=5=E5=Eg02Z6'B%A03?%>0PE1RE>P7%QECP%LE%KER01:E4R415E1'7,60%E6R6P01:E3R315E;'7,60P6ADE34%12#0#1#0#2#1#0#1#1#1#0#2#8R2,5E'7,60C<C<1C0@P5P>g01EHR0g01U5R@'F1G5>=H0@dg01HW=IE7CJb3b4b5X0EX1E1@></92\:\B^0E^1EP5P<f4P7P>O4b2UUX7EX6Eo"). Qed.

Local Lemma argv_mod_arith : forall s m : Z,
  (0 <= s)%Z -> (0 <= m)%Z -> (m <= 2107576)%Z -> (s + 4300000 < 2^64)%Z ->
  (0 <= s + m < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SeqExec ()) ["WithFP1"] "h02Hah14__x1h24__x2h37__arithh44__ffh56__sat3h66__sat4h78__varmaph85__with91mh:1sp;1p;2p;3p;4p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p6051001RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p60521000R=P9p8P=P5p8P=P0p8P=P@p8p100EEp6051000R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp6051001REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp60521000RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8p100H`p4p7210R@P7p8P@P:p8P@P;p8P@P5p8P@p100ILp4p710p8P@p100Iip4p710p8P@p100K0p4p710p8p100L:p4p710P5p8p100LUp4p70R@P1p8P@P2p8P@P7p8P@P:p8P@P;p8P@P4p8P@P3p8P@P<p8P@P5p8P@P6p8P>P5p8PEP7p8PEP5p8g00Mkj11Tg00NPj10Tg00USj19Tg02>fj2ATg02>Ij2>Tg02;Mj2MTg02B7j25Tg02AOj2HTg02BSj3GTg01LVj1:Tg02C7j26Tg02C`j3<Tg02DIj2CTg00]ej1WTg01TUj3BTg00MKj1VTg02E5j2UTg02ESj1RTg02F1j4QTg02FOj1NTg02Fmj1LTg02H;j2@Tg02GXj27Tg02T9j3?Tg00O5j1JTg02H^j3ITg02IAj4=Tg012gj1KTg02fCj7FTg02Ilj2ETg01:lj2OTg02JNj2PTg00R<j3DTg02K:j3STg02KYj4TTg02Naj2ZTg02SUj7YTg02T\j8XTg01HWR5f0RE'Ap=4%1E#1p=2f1R7g02VKR>g02VjR6P6g02WJR@PEg02WjFYp=3g01G4R<P7g02UdPEC=p=;f3R3P>P6P6P@f2R4P7PEGXp=8%47R;g01DcR:#1R2#2#2R1#1RB#1#0#1#0#1#2#0#1#0#0#0#1#2#9R0,A4R=f4R?%01#0#2#0#0#0#2#0#0#0#1#2#2#9R1'>%92R8%9BR9'MRA'51H891558%49155A[[%48RDg02XnRCAG897UW0%4A\C^0Dg02YJRDg01V`RC#:R9#:RF,6<16<916<CRC5<<5<<g02Z6R9'C%:FRF#:,6<16<F=<<C5<</C9%WD5BD3B%VDP<1U<4P7%R<CQ%N<%L<RDP<1@<:R:17<15?<g02ZbR917<8%JB5I<RBC=,3D%K6R8PD1@<2R217<0';,3DP8PD17<5R0/;2,3DP8PD1;0:,3DP8PDP>P6P6P@A?<:2R2,;0,3DP<P2P9PBC=,3DFFC8C8C8C81ED@PEP4g01EHRDg01U5R@'O1PE4=DD@dAS<57CTb4b7b8X1<X2<1>E1/5A%43R1f5R7,>?R5#4155A'Z\1[\=[^1<^2<PEf7f8P3P?P7f6O6b3b5b6UUV;UX9<X:<o"). Qed.

Local Lemma argv_final_arith : forall s m l : Z,
  (0 <= m)%Z -> (0 <= l)%Z -> (m <= 2107576)%Z -> (l <= 131071)%Z ->
  (s + 4300000 < 2^64)%Z ->
  (s <= s + m)%Z /\ (s + m + l + 1 < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SeqExec ()) ["WithFP1"] "h02Hah14__x1h24__x2h34__x3h47__arithh54__ffh66__sat4h76__sat5h88__varmaph95__with:1lh;1mh<1sp;2p;1p;3p;4p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p6051001RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p60521000R=P9p8P=P5p8P=P0p8P=P@p8p100EEp6051000R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp6051001REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp60521000RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8p100H`p4p7210R@P7p8P@P:p8P@P;p8P@P5p8P@p100ILp4p710p8P@p100Iip4p710p8P@p100K0p4p710p8p100L:p4p710P5p8p100LUp4p70R@P1p8P@P2p8P@P7p8P@P:p8P@P;p8P@P4p8P@P3p8P@P<p8P@P5p8P@P6p8P>P5p8PEP7p8PEP5p8g02>fj24Tg00Mkj12Tg00NPj11Tg00USj17Tg02>Ij29Tg02;Mj2JTg02B7j28Tg02AOj2GTg02BSj3FTg01LVj1=Tg02C7j2>Tg02C`j3ATg02DIj2WTg00]ej1VTg01TUj3UTg00MKj1TTg02E5j2BTg02F1j4OTg02FOj1NTg02Fmj1LTg02H;j2@Tg02GXj25Tg02T9j3;Tg00O5j1ITg02H^j3HTg02IAj4?Tg012gj1KTg02fCj7ETg02Ilj2MTg01:lj2DTg02JNj2PTg00R<j3QTg02K:j3CTg02KYj4RTg02Naj2STg02SUj7YTg02T\j8XTf0R5#2#2p=3%15#1p=0f1REg02VKR7g02VjR>P>g02WJR6P5g02WjFYp=6g01G4R@PEg02UdP5C?p=:f3R<P7P>P>P6f2R3PEP5GXp=<g01HWR4/4ER;g01DcR:#2R2#3#3R1#2RB#2#1#2#1#2#3#1#2#1#0#2#3#7R0,4<R=%1:R?#1#0#0#0#0#0#0#0#7R8,4<R9f6RA%01#3#1#0#3#1#0#2#3#3#7R1'9%72RD%7BRC'JRF'81GDC184D144C184F[[144DRGg02XnRHAFDCEUW0144F\H^0Gg02YJRGg01V`RH#=#=RC#=RI#=,>@1>@I1>@C1>@H5A@5A@5A@g02Z6'W%VG3U%TGP@1B@3PE1B@<CO%N@%L@RGP@1@@:RH15@15;@g02ZbRC15@D%IB5H@RBC?,6G%K>RDPG1@@?R?15@8':,6GPDPG1@@2R215@0':,6GPDPG15@4/:2,6GPDPGP7P>P>P6A;@H2R2,:H,6GP@A;@2?%7:R:,5@5;@PCPBC?,6GFEC<C<C<C<1MG6P5P3g01EHRGg01U5R6'D1P53=QG6dAC@4ECRb5b8b9X1@X2@X3@1951/8Ff4R1,44f5R4,91RE,4119EA/9:/8F'S[\=\9[^1@^2@^3@P5f8f9f:P<P1P4f7O7b4b6b7UUUV;UX:@X;@X<@o"). Qed.

Lemma argv_ptr_bounds : forall v inp mbase (sp brk : word) draw k,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  (bv_unsigned sp
   <= bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                     (in_execfn inp) k))%Z
  /\ (bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                     (in_execfn inp) k)
      + Z.of_nat (length (nth k (in_argv inp) [])) + 1 < 2 ^ 64)%Z.
Proof.
  intros v inp mbase sp brk draw k Hlaunch Hk.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch) as HA.
  pose proof (u_cat_string_base v inp mbase sp brk draw Hlaunch) as Hu.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Nat2Z.is_nonneg
    (total_arg_bytes_nat (firstn k (in_argv inp)))).
  assert (Hstr : (Z.of_nat (total_arg_bytes_nat (firstn k (in_argv inp)))
                  + Z.of_nat (length (nth k (in_argv inp) [])) + 1
                  <= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                 (in_execfn inp)))%Z).
  { pose proof (total_arg_bytes_firstn_within (in_argv inp) k Hk) as Hw.
    unfold launch_string_bytes. rewrite length_flatten_strings.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings (in_envp inp)))).
    pose proof (Nat2Z.is_nonneg (length (in_execfn inp))).
    lia. }
  rewrite (cat_argv_ptr_offset _ _ _ _ k Hk), word_add_nat_Z2bv, Hu.
  rewrite u_Z2bv_lt by lia.
  split; lia.
Qed.

(* [comment removed for export] *)
Lemma step_jalr_x0 : forall segs regs pc mem rom w rs1 (imm : bv 12) tgt,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr 0 rs1 imm, 4%Z) ->
  getr regs rs1 = tgt ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_jalr tgt (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 imm tgt Hf He Hd Ht.
  rewrite (step_jalr segs regs pc mem rom w 0 rs1 imm Hf He Hd).
  rewrite Ht. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_jalr_link : forall segs regs pc mem rom w rd rs1 (imm : bv 12) tgt,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  getr regs rs1 = tgt ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (v_addi pc 4)) (v_jalr tgt (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 imm tgt Hf He Hd Hrd Ht.
  rewrite (step_jalr segs regs pc mem rom w rd rs1 imm Hf He Hd).
  rewrite Ht, Hrd. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma getr_zero : forall regs, getr regs 0 = Z_to_bv 64 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
End WithFP1.
Ltac reg_neq_tac :=
  let Hc := fresh "Hc" in intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate Hc.

Section WithFP2.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP2.
Ltac getr_resolve :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero;
  rewrite ?getr_nz by reg_neq_tac.

Section WithFP3.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP3.
Ltac regupd_resolve :=
  repeat first [ rewrite regupd_same
               | rewrite regupd_other by reg_neq_tac ].

Section WithFP4.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Goal forall regs (v : word), getr (regupd (regupd regs 8 v) 9 v) 8 = v.
Proof. intros. getr_resolve. reflexivity. Abort.
Goal forall regs (v : word), getr (regupd regs 8 v) 0 = Z_to_bv 64 0.
Proof. intros. getr_resolve. reflexivity. Abort.
Goal forall regs (v : word), reg_get (regupd (regupd regs 8 v) 9 v) 8 = v.
Proof. intros. regupd_resolve. reflexivity. Abort.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition v_divu (x y : word) : word :=
  Z_to_bv 64 (bv_unsigned x / bv_unsigned y).
Definition v_remu (x y : word) : word :=
  Z_to_bv 64 (bv_unsigned x mod bv_unsigned y).

(* [comment removed for export] *)
Lemma m_divu : forall a b : word, (bv_unsigned b <> 0)%Z ->
  mul_div M_DIVU a b = v_divu a b.
Proof.
  intros a b Hb.
  change (mul_div M_DIVU a b)
    with (if (bv_unsigned b =? 0)%Z then Z_to_bv 64 (-1) else bv_divu a b).
  rewrite (proj2 (Z.eqb_neq _ _) Hb).
  apply bv_eq. unfold v_divu.
  rewrite bv_divu_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z.
  pose proof (u64_range a). pose proof (u64_range b).
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with (bv_unsigned a); [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma m_remu : forall a b : word, (bv_unsigned b <> 0)%Z ->
  mul_div M_REMU a b = v_remu a b.
Proof.
  intros a b Hb.
  change (mul_div M_REMU a b)
    with (if (bv_unsigned b =? 0)%Z then a else bv_modu a b).
  rewrite (proj2 (Z.eqb_neq _ _) Hb).
  apply bv_eq. unfold v_remu.
  rewrite bv_modu_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z.
  pose proof (u64_range a). pose proof (u64_range b).
  pose proof (Z.mod_pos_bound (bv_unsigned a) (bv_unsigned b) ltac:(lia)).
  lia.
Qed.

Lemma step_divu : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_DIVU rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs2) <> 0)%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (v_divu (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz.
  erewrite step_mul_gen by eassumption.
  rewrite m_divu by exact Hnz. reflexivity.
Qed.

Lemma step_remu : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_REMU rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs2) <> 0)%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (v_remu (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz.
  erewrite step_mul_gen by eassumption.
  rewrite m_remu by exact Hnz. reflexivity.
Qed.

Lemma step_lw_zero : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat
    = Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4) mem rom).
Proof.
  (* 727298f3:theories/Common/SeqExec.v, [step_lw_zero]: the recorded term no
     longer typechecks against this tree's load step at the revision. *)
  intros segs regs pc mem rom w rd rs imm Hf He Hd Hrd Hr.
  assert (Hval : sext 64 (bv_extract 0 32 (le_bytes_to_word
                    [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]))
                 = Z_to_bv 64 0)
    by (apply bv_eq; reflexivity).
  step_pipeline Hf He Hd.
  rewrite bv_eqb0_is_x0 in Hrd.
  unfold getr in Hr; rewrite ?bv_eqb0_is_x0 in Hr.
  rewrite ov_rdn, b_addsext, Hr; cbv beta iota.
  rewrite Hval, Hrd; cbv beta iota.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sb : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 1 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  assert (Hsb : forall u : word,
    Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
  { intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
    f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_wrap. lia. }
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, Hsb, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sb256 : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 1 (getr regs rs2))) rom).
Proof. exact step_sb. Qed.

(* [comment removed for export] *)
Lemma N_to_le_bytes_1_small : forall v : word,
  word_to_le_bytes 1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Zmod_pow2_div8 : forall z m, (8 <= m)%Z ->
  ((z mod 2^m) / 2^8)%Z = ((z / 2^8) mod 2^(m-8))%Z.
Proof.
  intros z m Hm.
  rewrite <- !Z.shiftr_div_pow2 by lia.
  apply Z.bits_inj'; intros i Hi.
  rewrite !Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases i (m - 8)) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_wrap : forall n (m : N) z,
  (8 * Z.of_nat n <= Z.of_N m)%Z ->
  Z_to_le_bytes n (bv_wrap m z) = Z_to_le_bytes n z.
Proof.
  induction n as [|n IH]; intros m z Hm; cbn [Z_to_le_bytes]; [reflexivity|].
  f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned.
    apply bv_wrap_bv_wrap. lia.
  - replace (Z.shiftr (bv_wrap m z) 8) with (bv_wrap (m - 8) (Z.shiftr z 8)).
    + apply IH. lia.
    + unfold bv_wrap, bv_modulus.
      rewrite !Z.shiftr_div_pow2 by lia.
      rewrite Zmod_pow2_div8 by lia.
      do 2 f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma store_bytes_low16 : forall u : word,
  Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 u)) = word_to_le_bytes 2 u.
Proof.
  intro u. unfold word_to_le_bytes.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply Z_to_le_bytes_wrap. lia.
Qed.

(* [comment removed for export] *)
Lemma store_bytes_low32 : forall u : word,
  Z_to_le_bytes 4 (bv_unsigned (low32 u)) = word_to_le_bytes 4 u.
Proof.
  intro u. unfold low32, word_to_le_bytes.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply Z_to_le_bytes_wrap. lia.
Qed.

(* [comment removed for export] *)
Lemma step_sw_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sw_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 v)) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sw_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)
Lemma step_sh_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ2 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 2%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 2 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low16, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sh_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ2 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 2%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 2 v)) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sh_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_divu_small : forall x y : word, (0 < bv_unsigned y)%Z ->
  bv_unsigned (v_divu x y) = (bv_unsigned x / bv_unsigned y)%Z.
Proof.
  intros x y Hy. unfold v_divu.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z.
  pose proof (u64_range x). pose proof (u64_range y).
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with (bv_unsigned x); [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma v_remu_small : forall x y : word, (0 < bv_unsigned y)%Z ->
  bv_unsigned (v_remu x y) = (bv_unsigned x mod bv_unsigned y)%Z.
Proof.
  intros x y Hy. unfold v_remu.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z.
  pose proof (u64_range y).
  pose proof (Z.mod_pos_bound (bv_unsigned x) (bv_unsigned y) Hy).
  lia.
Qed.

Lemma v_subw_small : forall x y : word,
  (bv_unsigned y <= bv_unsigned x)%Z ->
  (bv_unsigned x - bv_unsigned y < 2^31)%Z ->
  bv_unsigned (v_subw x y) = (bv_unsigned x - bv_unsigned y)%Z.
Proof.
  intros x y Hle Hlt. unfold v_subw.
  rewrite Z_to_bv_unsigned.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Lemma land_d48 : forall d : Z, (0 <= d)%Z -> (d < 16)%Z -> Z.land d 48 = 0%Z.
Proof.
  intros d Hd0 Hd. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 4) as [Hi4|Hi4].
  - replace 48%Z with (Z.shiftl 3 4)%Z by reflexivity.
    rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite (Z_testbit_high 4 d i) by lia. reflexivity.
Qed.

Lemma lor_small_add : forall d : Z, (0 <= d)%Z -> (d < 16)%Z ->
  Z.lor d 48 = (d + 48)%Z.
Proof.
  intros d Hd0 Hd.
  rewrite <- Z.lxor_lor by (apply land_d48; assumption).
  rewrite <- Z.add_nocarry_lxor by (apply land_d48; assumption).
  reflexivity.
Qed.

Lemma v_ori_lor : forall d : word, (bv_unsigned d < 16)%Z ->
  v_ori d 48 = Z_to_bv 64 (bv_unsigned d + 48).
Proof.
  intros d Hd. unfold v_ori.
  change (bv_wrap 64 48) with 48%Z.
  f_equal. apply lor_small_add; [apply u64_range | exact Hd].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_app : forall segs mem n1 n2 (a : word) bs1 bs2,
  rdn segs mem a n1 = Some bs1 ->
  rdn segs mem (a + nat_to_word n1) n2 = Some bs2 ->
  rdn segs mem a (n1 + n2)%nat = Some (bs1 ++ bs2).
Proof.
  intros segs mem n1. induction n1 as [|n1 IH]; intros n2 a bs1 bs2 H1 H2.
  - cbn in H1. injection H1 as <-. cbn [app].
    rewrite word_add_0 in H2. exact H2.
  - change (S n1 + n2)%nat with (S (n1 + n2))%nat.
    cbn [rdn] in H1 |- *.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|]; [|discriminate].
    destruct (rdn segs mem (a+1) n1) as [rest|] eqn:Er; [|discriminate].
    injection H1 as <-.
    rewrite (IH n2 (a+1) rest bs2 Er); [reflexivity|].
    replace (a + 1 + nat_to_word n1) with (a + nat_to_word (S n1))
      by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
    exact H2.
Qed.

Lemma rdn_nth : forall segs mem n (a : word) bs j,
  rdn segs mem a n = Some bs -> (j < n)%nat ->
  rdn segs mem (a + nat_to_word j) 1%nat = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs j H Hj; [lia|].
  cbn [rdn] in H.
  destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
    as [b|] eqn:Eb; [|discriminate].
  destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
  injection H as <-.
  destruct j as [|j].
  - rewrite word_add_0. cbn [rdn nth]. rewrite Eb. reflexivity.
  - cbn [nth].
    replace (a + nat_to_word (S j)) with (a + 1 + nat_to_word j)
      by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
    apply (IH (a+1) rest j Er). lia.
Qed.

(* [comment removed for export] *)
Lemma v_addi_m : forall (x : word) (k : Z),
  (k <= bv_unsigned x)%Z -> (0 < k)%Z ->
  v_addi x (- k) = Z_to_bv 64 (bv_unsigned x - k).
Proof. intros x k _ _. reflexivity. Qed.

Lemma rdn_skipn : forall segs mem n (a : word) bs k,
  rdn segs mem a n = Some bs -> (k <= n)%nat ->
  rdn segs mem (a + nat_to_word k) (n - k)%nat = Some (skipn k bs).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
  - assert (k = 0)%nat by lia. subst k. rewrite word_add_0.
    cbn in H |- *. injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct k as [|k].
    + rewrite word_add_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
    + cbn [Nat.sub skipn].
      replace (a + nat_to_word (S k)) with (a + 1 + nat_to_word k)
        by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
      apply (IH (a+1) rest k Er). lia.
Qed.

Lemma rdn_firstn : forall segs mem n (a : word) bs k,
  rdn segs mem a n = Some bs -> (k <= n)%nat ->
  rdn segs mem a k = Some (firstn k bs).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
  - assert (k = 0)%nat by lia. subst k. cbn in H |- *.
    injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct k as [|k]; [reflexivity|].
    cbn [rdn firstn]. rewrite Eb.
    rewrite (IH (a+1) rest k Er) by lia. reflexivity.
Qed.
End WithFP4.

End SeqExec.
Module StreamExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_StreamExec () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsCeq_rewrite_relationI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes;EquivalenceEpointwise_equivalenceC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:Proper_mapc59OSSVerify5KrLib7Mh_00387CatExec=flat_map_app'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00387CatExec9skipn_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_00387CatExec>flat_map_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltc59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00c59OSSVerify5KrLib7Mh_00387CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memc59OSSVerify5KrLib7Mh_00387CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExec<wbytes_aboveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib7Mh_0038:StreamExecBwrite_to_mem_aboveC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01c59OSSVerify5KrLib7Mh_0038:StreamExecBwrite_to_mem_belowC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib7Mh_00387SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K45stdpp9bitvector;definitions2bv01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC45stdpp9bitvector;definitions6bv_addC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC49OSSVerify5KrLib8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesc59OSSVerify5KrLib7Mh_0038:StreamExec?adv_apply_writeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_lui_4096 : v_lui 4096 = Z_to_bv 64 4096.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma c_lts_0_0 : c_lts (Z_to_bv 64 0) (Z_to_bv 64 0) = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma write_to_mem_below : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  (bv_unsigned a < bv_unsigned buf)%Z ->
  write_to_mem mem buf data a = mem a.
Proof.
  intros data mem buf a Hnw Ha.
  rewrite write_to_mem_wbytes. apply wbytes_below; assumption.
Qed.

(* [comment removed for export] *)
Lemma write_to_mem_above : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z ->
  write_to_mem mem buf data a = mem a.
Proof.
  intros data mem buf a Ha.
  rewrite write_to_mem_wbytes. apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
Lemma rdn_wtm_out : forall segs data m (buf a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  ((bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z \/
   (bv_unsigned a + Z.of_nat n <= bv_unsigned buf)%Z) ->
  rdn segs (write_to_mem m buf data) a n = rdn segs m a n.
Proof.
  intros segs data m buf a n Hna Hnb Hd. apply rdn_ext; [exact Hna|].
  intros x Hx. destruct Hd as [Hd | Hd].
  - apply write_to_mem_above. lia.
  - apply write_to_mem_below; [exact Hnb | lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_write_to_mem : forall segs data mem (buf : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  rdn segs (write_to_mem mem buf data) buf (length data) = Some data.
Proof.
  intros segs data mem buf Hnw.
  rewrite write_to_mem_wbytes. apply rdn_wbytes_hit. exact Hnw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_apply_write : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret [(buf, data)] []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
  intros regs pc sv mem rom ret buf data.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma adv_apply_delivered : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret (delivered_writes buf data) []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
  intros regs pc sv mem rom ret buf data.
  destruct data as [|b rest]; [|apply adv_apply_write].
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes
       delivered_writes write_to_mem].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.
End WithFP1.

End StreamExec.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence OmniEquivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun. From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Prelude. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.
Module WallSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WallSim () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsCeq_rewrite_relationI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes;EquivalenceEpointwise_equivalenceC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:Proper_mapc59OSSVerify5KrLib7Mh_00387CatExec=flat_map_app'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00387CatExec9skipn_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_00387CatExec>flat_map_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordI47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=Z_to_bv_smallC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib5Lists4List@firstn_length_lec59OSSVerify5KrLib7Mh_00387WallSim:u_len_wordC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAlen_word_unsignedC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z6inj_leC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions?bv_add_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib7Mh_00387WallSimClen_word_firstn_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSimAu_len_word_firstnC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<length_skipnC49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC49OSSVerify5KrLib8PropExec;v_sub_smallC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00387WallSim7to_wall10C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01k59OSSVerify5KrLib7Mh_00387WallSim7to_wall13C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:msteps_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01i59OSSVerify5KrLib7Mh_00387WallSim7to_wall00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSim@to_wall_tail_indC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00306CatSim6fdchanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim;buf_modeledC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K4ELinuxProcessSemantics?LinuxProcessSem5State5event02K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC59OSSVerify5KrLib7Mh_00306CatSimBsstep_write_ch_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c59OSSVerify5KrLib7Mh_00387WallSimAsstep_to_wall_invC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C46Stdlib5Lists4List9skipn_allC56Stdlib5Arith8PeanoNat3Nat7le_reflC59OSSVerify5KrLib7Mh_00306CatSimAbuf_modeled_skipnC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00C46Stdlib5Lists4List:firstn_allK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC59OSSVerify5KrLib7Mh_00306CatSim=write_ch_ok_nC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04C59OSSVerify5KrLib7Mh_00306CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run4star02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepC4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01c59OSSVerify5KrLib7Mh_00387WallSim>to_wall_mutindC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00c59OSSVerify5KrLib7Mh_00387WallSimGto_wall_star_admits_mutC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List7map_appC46Stdlib5Lists4List<firstn_skipnC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClassesEEquivalence_ReflexiveC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC59OSSVerify5KrLib7Mh_00307ExitSim?sstep_instr_invC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_Reflexivec59OSSVerify5KrLib7Mh_00387WallSimEto_wall_star_only_mutC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsc59OSSVerify5KrLib7Mh_00387CatExec7adv_setC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387WallSim7to_wall01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSim@to_wall_k_ex_mutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSim;to_wallexitC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01c59OSSVerify5KrLib7Mh_00387WallSimAto_wall_tail_k_exC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02K59OSSVerify5KrLib7Mh_00306CatSim8to_wexit03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim?msteps_to_wexitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSimCmsteps_to_wall_tailC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec00K4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome02C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_conseqK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec02C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun>exec_step_onlyC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4postI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome00C46Stdlib5Lists4List9app_nil_rI59OSSVerify5KrLib7Mh_00306CatSim8to_wexit00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib7Mh_00307ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC59OSSVerify5KrLib7Mh_00307ExitSimBin_sysno_sys_inputC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00307ExitSim@exit_dispatch_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_killed_with_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep06C59OSSVerify5KrLib7Mh_00307ExitSim>sstep_exit_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_halted_with_haltedC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exits_withC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec01C59OSSVerify5KrLib7Mh_00306CatSim<to_wexit_indC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03c59OSSVerify5KrLib7Mh_00387WallSimEto_wexit_nil_exec_auxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<bufs_modeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSimAto_wexit_nil_execC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffc59OSSVerify5KrLib7Mh_00387WallSim@to_wall_exec_mutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:wevents_chC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSim@to_wallexit_execC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_realizesI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun5mexec00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun?mexec_halt_starC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exec_soundC47Corelib4Init5Logic6eq_symI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6cosafe00c59OSSVerify5KrLib7Mh_00387WallSimGto_wallexit_star_admitsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;cosafe_starC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun9exec_starC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunGexits_with_never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_no_errorC59OSSVerify5KrLib7Mh_00306CatSim7weventsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateC4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun8omni_runI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun8is_errorc59OSSVerify5KrLib7Mh_00387WallSim=wall_omni_runC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<exec_obs_iffC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<img_segmentsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:omni_corunC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence:omni_equivC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_coexecC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunDnever_errors_coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=coexec_conseqC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence@omni_trace_equivC4ELinuxProcessSemantics?LinuxProcessSem3Run3runC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalenceDtrace_equiv_iff_omniC4ELinuxProcessSemantics?LinuxProcessSem3Run9obs_traceC47Corelib4Init5Logic3iffc59OSSVerify5KrLib7Mh_00387WallSim<wall_obs_iffC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=bh_errors_iffc59OSSVerify5KrLib7Mh_00387WallSimAwall_no_error_runC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitK47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitc59OSSVerify5KrLib7Mh_00387WallSim6fd32_1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6errorsI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_ReflexiveC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence7modeledC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence5equivC59OSSVerify5KrLib7Mh_00266SimInvDno_error_run_modeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=bh_all_errors".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Lemma fd32_1 : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma fd32_2 : fd32 (Z_to_bv 64 2) = Z_to_bv 64 2.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
  intros A l H. unfold len_word. apply Z_to_bv_small.
  unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia.
Qed.

(* [comment removed for export] *)

Lemma len_word_firstn_nat : forall n (bs : list byte),
  (n <= length bs)%nat ->
  len_word (firstn n bs) = nat_to_word n.
Proof.
  intros n bs Hn. unfold len_word, nat_to_word.
  rewrite firstn_length_le by exact Hn. reflexivity.
Qed.

Lemma u_len_word_firstn : forall n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  bv_unsigned (len_word (firstn n bs)) = Z.of_nat n.
Proof.
  intros n bs Hn Hlen.
  rewrite len_word_unsigned by (rewrite firstn_length_le by exact Hn;
                                unfold two_pow_64; lia).
  rewrite firstn_length_le by exact Hn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_add_len_firstn : forall (p : word) n (bs : list byte),
  (n <= length bs)%nat ->
  v_add p (len_word (firstn n bs)) = p + nat_to_word n.
Proof.
  intros p n bs Hn. rewrite len_word_firstn_nat by exact Hn.
  unfold v_add. apply bv_eq.
  rewrite Z_to_bv_unsigned, bv_add_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_add_len_firstn_Z : forall (p : word) n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  v_add p (len_word (firstn n bs)) = Z_to_bv 64 (bv_unsigned p + Z.of_nat n).
Proof.
  intros p n bs Hn Hlen. unfold v_add.
  rewrite u_len_word_firstn by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma word_add_nat_Z : forall (p : word) (k : nat),
  (Z.of_nat k < 2^64)%Z ->
  p + nat_to_word k = Z_to_bv 64 (bv_unsigned p + Z.of_nat k).
Proof.
  intros p k Hk. apply bv_eq.
  rewrite bv_add_unsigned. unfold nat_to_word.
  rewrite Z_to_bv_small
    by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_sub_len_firstn : forall n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  v_sub (len_word bs) (len_word (firstn n bs)) = len_word (skipn n bs).
Proof.
  intros n bs Hn Hlen. apply bv_eq.
  rewrite v_sub_small
    by (rewrite u_len_word_firstn by assumption;
        rewrite len_word_unsigned by (unfold two_pow_64; lia); lia).
  rewrite u_len_word_firstn by assumption.
  rewrite !len_word_unsigned
    by (unfold two_pow_64; rewrite ?length_skipn; lia).
  rewrite length_skipn. lia.
Qed.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
         (skipn n rest) k) ->
    to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
    (1 <= length rest)%nat ->
    to_wall ms rest k ->
    to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wall_tail ms' rest k ->
    to_wall_tail ms rest k.

Scheme to_wall_min := Minimality for to_wall Sort Prop
  with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.

(* [comment removed for export] *)
Lemma msteps_to_wall_tail : forall ms ms' rest k,
  msteps segs ms ms' -> to_wall_tail ms' rest k -> to_wall_tail ms rest k.
Proof.
  intros ms ms' rest k H; induction H; [auto|].
  intro Hw. eapply twt_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma to_wall_tail_nil_msteps : forall ms k,
  to_wall_tail ms [] k -> exists ms', msteps segs ms ms' /\ k ms'.
Proof.
  intros ms k H.
  remember ([] : list byte) as rest eqn:Hrest.
  induction H as [ms k Hk | ms rest k Hnb Hw | ms ms' rest k Hsvc Hstep Ht IH].
  - exists ms. split; [apply mst_refl | exact Hk].
  - subst rest. cbn in Hnb. lia.
  - destruct (IH Hrest) as (ms'' & Hm & Hk).
    exists ms''. split; [eapply mst_step; eauto | exact Hk].
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_to_wall_inv : forall ms rest k model evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  buf_modeled rest ->
  to_wall ms rest k ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length rest)%nat /\
    evs = map (WriteEv ch) (firstn n rest) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model) /\
    to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
      (skipn n rest) k.
Proof.
  intros ms rest k model evs st Hh Hlazy Hfdc Hbm Hw Hss.
  revert Hbm.
  destruct Hw as [ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont]. intro Hbm.
  destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs st
              Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hst).
  exists n. repeat split; try assumption.
  apply (Hcont n Hn1 Hn2).
Qed.

Lemma to_wall_no_error_sstep : forall ms rest k model evs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  buf_modeled rest ->
  to_wall ms rest k ->
  ~ sstep segs (mkCfg ms model) evs SError.
Proof.
  intros ms rest k model evs Hh Hlazy Hfdc Hbm Hw Hss.
  destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
    as (n & _ & _ & _ & Hst & _).
  discriminate Hst.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wall_star_admits_mut : forall model tr_k,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms rest k, to_wall ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
     exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
  /\ (forall ms rest k, to_wall_tail ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
     exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c).
Proof.
  intros model tr_k Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
       exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
       exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)).
  - (* twl_write: deliver everything in one syscall *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm Hk.
    destruct (IH (length rest) Hnb (Nat.le_refl _)
                (buf_modeled_skipn (length rest) rest Hbm) Hk) as [c Hstar].
    exists c.
    replace (map (WriteEv ch) rest ++ tr_k)
      with (map (WriteEv ch) (firstn (length rest) rest)
              ++ (map (WriteEv ch) (skipn (length rest) rest) ++ tr_k))
      by (rewrite firstn_all, skipn_all; reflexivity).
    eapply star_step; [| exact Hstar].
    rewrite <- (apply_effect_copyins_no_write ms
                  (len_word (firstn (length rest) rest))
                  [(ms_gpr ms 1, length rest)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, length rest)]
                (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
             (map (WriteEv ch) (firstn (length rest) rest)));
      [exact Hh | exact Hsvc | | exact Hh |].
    eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
    rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
  - (* twt_done: hand off to the continuation *)
    intros ms k Hk Hbm Hcont. cbn [map app]. apply (Hcont ms Hk).
  - (* twt_more *)
    intros ms rest k Hnb Hw IH Hbm Hk. exact (IH Hbm Hk).
  - (* twt_step *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm Hk.
    destruct (IH Hbm Hk) as [c Hstar].
    exists c.
    replace (map (WriteEv ch) rest ++ tr_k)
      with (([] : list event) ++ (map (WriteEv ch) rest ++ tr_k)) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_wall_star_admits : forall ms rest k,
  to_wall ms rest k ->
  buf_modeled rest ->
  forall model tr_k,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
  exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c.
Proof.
  intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
  exact (proj1 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.

Lemma to_wall_tail_star_admits : forall ms rest k,
  to_wall_tail ms rest k ->
  buf_modeled rest ->
  forall model tr_k,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
  exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c.
Proof.
  intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
  exact (proj2 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wall_star_only_mut : forall model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms rest k, to_wall ms rest k ->
     buf_modeled rest ->
     (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
     forall tr c, star segs (mkCfg ms model) tr c ->
     is_prefix tr (map (WriteEv ch) rest ++ T))
  /\ (forall ms rest k, to_wall_tail ms rest k ->
     buf_modeled rest ->
     (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
     forall tr c, star segs (mkCfg ms model) tr c ->
     is_prefix tr (map (WriteEv ch) rest ++ T)).
Proof.
  intros model T Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
       forall tr c, star segs (mkCfg ms model) tr c ->
       is_prefix tr (map (WriteEv ch) rest ++ T))
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
       forall tr c, star segs (mkCfg ms model) tr c ->
       is_prefix tr (map (WriteEv ch) rest ++ T))).
  - (* twl_write *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm HK tr c Hstar.
    inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    { apply is_prefix_nil. }
    destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs (SNext c2)
                Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc2).
    subst evs. inversion Hc2; subst c2.
    pose proof (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK tr2 c Hstar2) as Hp.
    rewrite <- (firstn_skipn n rest) at 2.
    rewrite map_app, <- app_assoc.
    apply is_prefix_app_mono. exact Hp.
  - (* twt_done *)
    intros ms k Hk Hbm HK tr c Hstar. cbn [map app]. exact (HK ms tr c Hk Hstar).
  - (* twt_more *)
    intros ms rest k Hnb Hw IH Hbm HK tr c Hstar. exact (IH Hbm HK tr c Hstar).
  - (* twt_step *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK tr c Hstar.
    inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    { apply is_prefix_nil. }
    destruct (sstep_instr_inv segs ms model ms' evs (SNext c2) Hlazy Hsvc Hstep Hss)
      as [Hevs Hc2].
    subst evs. inversion Hc2; subst c2. cbn [app].
    exact (IH Hbm HK tr2 c Hstar2).
Qed.

Lemma to_wall_star_only : forall ms rest k,
  to_wall ms rest k ->
  buf_modeled rest ->
  forall model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr (map (WriteEv ch) rest ++ T).
Proof.
  intros ms rest k Hw Hbm model T Hh Hlazy Hfdc HK tr c Hstar.
  exact (proj1 (to_wall_star_only_mut model T Hh Hlazy Hfdc) ms rest k Hw Hbm HK tr c Hstar).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma twl_write_rec : forall (k : machine_state -> Prop) rest regs pc mem rom,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = fd ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None;
                   ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some rest ->
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length rest)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
     to_wall_tail (mkst (regupd regs 10 (len_word (firstn n rest)))
                        (v_addi pc 4) mem rom)
       (skipn n rest) k) ->
  to_wall {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
             ms_svc_pending := Some (getr regs 17); ms_resv := None;
             ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    rest k.
Proof.
  intros k rest regs pc mem rom H17 H10 Hr Hok Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  eapply twl_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
    (ms : machine_state) : Prop :=
  match bufs with
  | [] => to_wexit segs ms [] code
  | buf :: rest =>
      (1 <= length buf)%nat /\
      to_wall_tail ms buf (to_wallexit rest code)
  end.

(* [comment removed for export] *)
Lemma to_wall_k_ex_mut :
  (forall ms rest k, to_wall ms rest k -> exists ms', k ms')
  /\ (forall ms rest k, to_wall_tail ms rest k -> exists ms', k ms').
Proof.
  apply (to_wall_mutind
           (fun ms rest k => exists ms', k ms')
           (fun ms rest k => exists ms', k ms')).
  - intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH.
    exact (IH (length rest) Hnb (Nat.le_refl _)).
  - intros ms k Hk. exists ms. exact Hk.
  - intros ms rest k Hnb Hw IH. exact IH.
  - intros ms ms' rest k Hsvc Hstep Ht IH. exact IH.
Qed.

Lemma to_wall_tail_k_ex : forall ms rest k,
  to_wall_tail ms rest k -> exists ms', k ms'.
Proof. exact (proj2 to_wall_k_ex_mut). Qed.

Lemma to_wallexit_bufs_nonempty : forall bufs code ms,
  to_wallexit bufs code ms ->
  Forall (fun b : list byte => (1 <= length b)%nat) bufs.
Proof.
  induction bufs as [|buf rest IH]; intros code ms Hw; [constructor|].
  destruct Hw as [Hnb Hw]. constructor; [exact Hnb|].
  destruct (to_wall_tail_k_ex _ _ _ Hw) as [ms' Hk].
  exact (IH code ms' Hk).
Qed.

(* [comment removed for export] *)
Lemma twe_step : forall ms ms' bufs code,
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
  intros ms ms' bufs code Hsvc Hstep Hw.
  destruct bufs as [|buf rest].
  - eapply tw_step; eauto.
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply twt_step; eauto.
Qed.

Lemma msteps_to_wallexit : forall ms ms' bufs code,
  msteps segs ms ms' -> to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
  intros ms ms' bufs code Hms Hw. destruct bufs as [|buf rest].
  - exact (msteps_to_wexit segs ms ms' [] code Hms Hw).
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply msteps_to_wall_tail; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wall_exec_mut : forall model (Q : post),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms rest k, to_wall ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
     OmniRun.exec segs (mkCfg ms model)
       (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
  /\ (forall ms rest k, to_wall_tail ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
     OmniRun.exec segs (mkCfg ms model)
       (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o)).
Proof.
  intros model Q Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
       OmniRun.exec segs (mkCfg ms model)
         (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
       OmniRun.exec segs (mkCfg ms model)
         (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))).
  - (* twl_write: every delivered length is a successor, each covered by the IH *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm HK.
    assert (Hw : to_wall ms rest k) by (eapply twl_write; eassumption).
    apply exec_step; [exact Hh | | |].
    + (* progress: deliver everything in one syscall *)
      eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length rest)]
                  (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
               (map (WriteEv ch) (firstn (length rest) rest)));
        [exact Hh | exact Hsvc | | exact Hh |].
      * eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
      * rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
    + intros evs Hss.
      destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
        as (n & _ & _ & _ & Habs & _).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_to_wall_inv ms rest k model evs (SNext c') Hh Hlazy Hfdc Hbm Hw Hss)
        as (n & Hn1 & Hn2 & -> & Hc' & _).
      injection Hc' as ->.
      eapply exec_conseq;
        [exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK) |].
      intros tr o (tr' & -> & HQ). exists tr'. split; [| exact HQ].
      rewrite <- (firstn_skipn n rest) at 3. rewrite map_app, <- app_assoc. reflexivity.
  - (* twt_done: the continuation's own judgment *)
    intros ms k Hk Hbm HK.
    eapply exec_conseq; [exact (HK ms Hk) |].
    intros tr o HQ. exists tr. split; [reflexivity | exact HQ].
  - (* twt_more *)
    intros ms rest k Hnb Hw IH Hbm HK. exact (IH Hbm HK).
  - (* twt_step: one silent instruction *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbm HK) |]. intros tr o H. cbn [app]. exact H.
Qed.

(* [comment removed for export] *)
Lemma to_wexit_nil_exec_aux : forall ms bufs code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms bufs code ->
  bufs = [] ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
  intros ms bufs code model Hh Hlazy Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH]; intro Hbufs; [| discriminate Hbufs |].
  - apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * cbn beta. rewrite app_nil_r. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbufs) |]. intros tr o H. cbn [app]. exact H.
Qed.

Lemma to_wexit_nil_exec : forall ms code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms [] code ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
  intros ms code model Hh Hlazy Hte.
  exact (to_wexit_nil_exec_aux ms [] code model Hh Hlazy Hte eq_refl).
Qed.

(* [comment removed for export] *)
Lemma to_wallexit_exec : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (m_fs model)]
                 /\ exits_with code tr o).
Proof.
  induction bufs as [|buf rest IH]; intros code ms model Hh Hlazy Hfdc Hbm Hw.
  - cbn [wevents_ch app]. apply to_wexit_nil_exec; assumption.
  - destruct Hw as [Hnb Hw]. apply Forall_cons_iff in Hbm as [Hb Hbs].
    eapply exec_conseq;
      [exact (proj2 (to_wall_exec_mut model _ Hh Hlazy Hfdc) ms buf (to_wallexit rest code)
                Hw Hb (fun ms' Hk => IH code ms' model Hh Hlazy Hfdc Hbs Hk)) |].
    intros tr o (tr' & -> & Heq & Hx). split; [| exact Hx].
    rewrite Heq. cbn [wevents_ch]. rewrite <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wallexit_star_admits : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  exists c, star segs (mkCfg ms model)
              (wevents_ch ch bufs ++ [ExitEv code (m_fs model)]) c.
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

(* [comment removed for export] *)
Lemma to_wallexit_no_other_exit : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall code', code' <> code ->
  ~ OmniRun.exec segs (mkCfg ms model) (exits_with code').
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw code' Hne Hex.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'.
  exact (Hne (eq_sym Hx')).
Qed.

Lemma to_wallexit_trace_unique : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall tr', tr' <> wevents_ch ch bufs ++ [ExitEv code (m_fs model)] ->
  ~ OmniRun.exec segs (mkCfg ms model) (fun tr _ => tr = tr').
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr' Hne Hex.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & o & Hm & Heq & _).
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Heq'. cbn beta in Heq'.
  apply Hne. rewrite <- Heq', Heq. reflexivity.
Qed.

Lemma to_wallexit_not_silent : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  ~ cosafe segs (mkCfg ms model) (fun tr => tr = []).
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw Hc.
  destruct (to_wallexit_star_admits bufs code ms model Hh Hlazy Hfdc Hbm Hw) as (c' & Hstar).
  pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
  destruct (wevents_ch ch bufs); discriminate Hnil.
Qed.

Lemma to_wallexit_star_only : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (m_fs model)]).
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) Hstar))
    as (tr' & o & _ & HQ).
  cbn beta in HQ. destruct HQ as (Heq & _). rewrite <- Heq. apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wallexit_no_error : forall ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model bufs code Hh Hlazy Hfdc Hbm Hw. apply exec_no_error.
  eapply exec_conseq; [exact (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegsCh.

(* [comment removed for export] *)
Abbreviation wexit1 segs ms bufs code :=
  (to_wallexit segs (Z_to_bv 64 1) bufs code ms).

(* [comment removed for export] *)
Lemma wevents_ch_fd1 : forall bufs,
  wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
  induction bufs as [|b bs IH]; cbn [wevents_ch wevents];
    [reflexivity | rewrite IH; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fdchan_with_vdso : forall v m fd ch, fdchan fd ch m -> fdchan fd ch (with_vdso v m).
Proof. intros v m fd ch H; exact H. Qed.

Lemma wall_omni_run : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit (run_segments segs inp sp mb) fd bufs code
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]
                 /\ exits_with code tr o).
Proof.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw.
  cbn [omni_run]. unfold init_config.
  exact (to_wallexit_exec (run_segments segs inp sp mb) fd ch Hfd32 bufs code _
           (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           eq_refl eq_refl (fdchan_with_vdso _ _ _ _ Hfdc) Hbm Hw).
Qed.

Lemma wall_obs_iff : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit (run_segments segs inp sp mb) fd bufs code
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  forall tr, obs_trace (run_segments segs inp sp mb)
               (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]).
Proof.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw tr.
  apply exec_obs_iff.
  eapply exec_conseq;
    [exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
  intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

Lemma wall_no_error_run : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit (run_segments segs inp sp mb) fd bufs code
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  ~ reaches_error (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw. apply exec_no_error.
  eapply exec_conseq;
    [exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma wall_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
  to_wallexit (run_segments source_segs inp rsp rmb) (Z_to_bv 64 1) bufs code
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) ->
  to_wallexit (run_segments target_segs inp asp amb) (Z_to_bv 64 1) bufs code
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) ->
  bufs_modeled bufs ->
  in_channel_reader inp = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
    Hsource Htarget Hbm Hr.
  assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp source_alloc_limit inp))
    by (apply fd1chan_fdchan, init_model_fd1chan; exact Hr).
  assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp target_alloc_limit inp))
    by (apply fd1chan_fdchan, init_model_fd1chan; exact Hr).
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (wall_omni_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 source_segs rpc rph rsp rbrk rmb rrnd
                source_alloc_limit inp bufs code HfdS Hbm Hsource) |].
    intros tr o (_ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code HfdS Hbm Hsource tr).
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget).
Qed.

(* [comment removed for export] *)
Lemma wall_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
  to_wallexit (run_segments source_segs inp rsp rmb) (Z_to_bv 64 1) bufs code
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) ->
  to_wallexit (run_segments target_segs inp asp amb) (Z_to_bv 64 1) bufs code
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) ->
  bufs_modeled bufs ->
  in_channel_reader inp = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         bufs code inp Hsource Htarget Hbm Hr.
  assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp rlim inp))
    by (apply fd1chan_fdchan, init_model_fd1chan; exact Hr).
  assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp alim inp))
    by (apply fd1chan_fdchan, init_model_fd1chan; exact Hr).
  split.
  { apply no_error_run_modeled.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
             HfdS Hbm Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
               HfdS Hbm Hsource tr).
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               target_segs apc aph asp abrk amb arnd alim inp bufs code
               HfdT Hbm Htarget tr).
    reflexivity.
  - cbn.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             target_segs apc aph asp abrk amb arnd alim inp bufs code
             HfdT Hbm Htarget).
Qed.
End WithFP1.

End WallSim.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Fs.ReadWrite.
Module StreamSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WallSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_StreamSim () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsCeq_rewrite_relationI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes;EquivalenceEpointwise_equivalenceC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:Proper_mapc59OSSVerify5KrLib7Mh_00387CatExec=flat_map_app'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00387CatExec9skipn_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_00387CatExec>flat_map_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00387WallSim:u_len_wordC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C47Corelib7Classes?RelationClasses;reflexivityI4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2eq00C5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch:lookup_armC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7sa_specC4ELinuxProcessSemantics?LinuxProcessSem5Monad9unmodeledC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite9read_specC47Corelib4Init5Logic3iffC4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes6option00I5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7SpecArm00C5ELinuxProcessSemantics?LinuxProcessSem3Sys<SyscallTable:spec_tableC47Corelib7Classes?RelationClasses=iff_ReflexiveC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@ms_writable_byteC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z4landC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_and_unsignedI47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic3and01I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib7Mh_00389StreamSim6M_loopC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC4ELinuxProcessSemantics?LinuxProcessSem5State;stream_takeC4ELinuxProcessSemantics?LinuxProcessSem5State:with_stdinI47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib7Mh_00306CatSim7fd1chanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init9Datatypes4andbK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC46Stdlib4Bool4Bool=andb_true_iffC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes7nat_indC4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_auxC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natc59OSSVerify5KrLib7Mh_00389StreamSim@wseg_ok_read_auxC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_mapC4ELinuxProcessSemantics?LinuxProcessSem5StateAread_bytes_map_eqC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeEread_bytes_map_prefixC4ELinuxProcessSemantics?LinuxProcessSem5State7in_wmemc59OSSVerify5KrLib7Mh_00389StreamSimAin_wmem_sys_inputC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203C4ELinuxProcessSemantics?LinuxProcessSem5State>rw_count_clampC4ELinuxProcessSemantics?LinuxProcessSem5State=stream_take_zC56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem5StateBstream_take_lengthI47Corelib4Init5Peano2le00C4ELinuxProcessSemantics?LinuxProcessSem5StateDrw_count_clamp_rangeC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8min_specI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z8max_specC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC4ELinuxProcessSemantics?LinuxProcessSem5State@stream_take_z_eqC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC4ELinuxProcessSemantics?LinuxProcessSem5State<MAX_RW_COUNTC4ELinuxProcessSemantics?LinuxProcessSem5State:access_okbC47Corelib4Init5Logic5proj1C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall9w_is0_posC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry05C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@modeled_rw_rangeC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7UaccessDcheck_access_ok_zeroC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWriteJcheck_socket_pending_errorC4ELinuxProcessSemantics?LinuxProcessSem5State:net_take_zC4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC4ELinuxProcessSemantics?LinuxProcessSem5State;pipe_lookupC4ELinuxProcessSemantics?LinuxProcessSem5State=pipe_end_liveC4ELinuxProcessSemantics?LinuxProcessSem5State9pipe_takeC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:writes_eqbC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem5State<pipe_consumeC4ELinuxProcessSemantics?LinuxProcessSem5State;pipe_insertC4ELinuxProcessSemantics?LinuxProcessSem5State:with_pipesK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWriteBcheck_read_urandomC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude;bv_eqb_reflC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWrite:check_readI6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00K4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream01I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00C4ELinuxProcessSemantics?LinuxProcessSem5State5EBADFI4ELinuxProcessSemantics?LinuxProcessSem5State5event00C4ELinuxProcessSemantics?LinuxProcessSem5State6EFAULTK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03C4ELinuxProcessSemantics?LinuxProcessSem5State6EISDIRI4ELinuxProcessSemantics?LinuxProcessSem5State9SockState00C4ELinuxProcessSemantics?LinuxProcessSem5State8ENOTCONNI4ELinuxProcessSemantics?LinuxProcessSem5State9NetStream00C4ELinuxProcessSemantics?LinuxProcessSem5State:ECONNRESETC4ELinuxProcessSemantics?LinuxProcessSem5State9ETIMEDOUTc59OSSVerify5KrLib7Mh_00389StreamSim;read0_wmem1C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event01c59OSSVerify5KrLib7Mh_00389StreamSim?read0_wmem_needC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude9listN_eqbC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude7wmem_okC4ELinuxProcessSemantics?LinuxProcessSem5State8net_takeK4ELinuxProcessSemantics?LinuxProcessSem5State9SockState04K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry07C4ELinuxProcessSemantics?LinuxProcessSem5StateFstream_take_nil_of_eofC47Corelib4Init5Logic8iff_reflK4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream02C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude?wmem_ok_of_fullC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<listN_eqb_eqC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6leb_leC5ELinuxProcessSemantics?LinuxProcessSem3Sys7UaccessDrw_count_clamp_of_rwK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01c59OSSVerify5KrLib7Mh_00389StreamSimAsyscall_spec_readC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim?read0_check_eofC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWriteCcheck_read_sound_okc59OSSVerify5KrLib7Mh_00389StreamSimAread0_check_bytesC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWriteFcheck_read_complete_okC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeEcheck_ret_only_ok_iffK47Corelib4Init5Logic2or01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC4ELinuxProcessSemantics?LinuxProcessSem5State9m_urandomC4ELinuxProcessSemantics?LinuxProcessSem5State5m_netC4ELinuxProcessSemantics?LinuxProcessSem5State9m_conn_ixK4ELinuxProcessSemantics?LinuxProcessSem5State7IoState01C4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01C4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqK47Corelib4Init5Logic2or02K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWriteMcheck_read_complete_unmodeledC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeKcheck_ret_only_no_unmodeledK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectc59OSSVerify5KrLib7Mh_00389StreamSim<read0_ok_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC59OSSVerify5KrLib7Mh_00306CatSimEapply_effect_no_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSimDm_vm_lazy_with_stdinC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedc59OSSVerify5KrLib7Mh_00389StreamSimCm_halted_with_stdinC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateIm_killed_of_m_halted_nonec59OSSVerify5KrLib7Mh_00389StreamSimBread0_no_unmodeledC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02i59OSSVerify5KrLib7Mh_00389StreamSim6chunks00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00389StreamSim6chunks02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim:chunks_indC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00389StreamSim6chunks01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim@stream_traces_chC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim:iter_ev_chC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim8eof_tailC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSimNstream_traces_ch_prefix_closedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00389StreamSim5to_wr00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepk59OSSVerify5KrLib7Mh_00389StreamSim5to_wr02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:msteps_indC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00387WallSim7to_wall10C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim6WrPendC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00387WallSim7to_wall00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387WallSim7to_wall12C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387WallSim7to_wall13C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim9to_wr_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim7lh_nextC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00389StreamSim5to_rd00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00389StreamSim5to_rd02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim<msteps_to_rdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim8ReadPendC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00K4ELinuxProcessSemantics?LinuxProcessSem3Run4star01C4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01K4ELinuxProcessSemantics?LinuxProcessSem3Run4star02c59OSSVerify5KrLib7Mh_00389StreamSim9to_rd_indC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib7Mh_00389StreamSim:to_rd_starC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00307ExitSimCto_exit_star_admitsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim<read0_ok_eofC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04C4ELinuxProcessSemantics?LinuxProcessSem3Run:star_transc59OSSVerify5KrLib7Mh_00389StreamSim;M_loop_takeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim>read0_ok_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim>fd1chan_fdchanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim6fdchanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim;buf_modeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim=lh_next_to_rdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim?to_wr_wall_tailC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSimHto_wall_tail_star_admitsC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02c59OSSVerify5KrLib7Mh_00389StreamSim7iter_evC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00307ExitSim7to_exit00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim9band0_255C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSim6fd32_1C1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib5Lists4List7map_appC46Stdlib5Lists4List9skipn_allc59OSSVerify5KrLib7Mh_00389StreamSim>sstep_read_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00307ExitSimAto_exit_star_onlyC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00307ExitSim?sstep_instr_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSimAsstep_to_wall_invC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib5Lists7ListDef5skipnc59OSSVerify5KrLib7Mh_00387WallSimGto_wall_tail_nil_mstepsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_allC47Corelib4Init3Nat3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib5Lists4List<length_skipnC59OSSVerify5KrLib7Mh_00306CatSimAbuf_modeled_skipnC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClassesEEquivalence_ReflexiveC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC46Stdlib5Lists4List<firstn_skipnC4ELinuxProcessSemantics?LinuxProcessSem3Run8star_indC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_Reflexivec59OSSVerify5KrLib7Mh_00389StreamSim4sinvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC59OSSVerify5KrLib7Mh_00307ExitSim7on_pathC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC59OSSVerify5KrLib7Mh_00307ExitSim<on_path_stepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSimFto_wall_no_error_sstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00307ExitSim@on_path_no_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00266SimInv8star_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim9sinv_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00266SimInvDinv_no_reaches_errorC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim=sinv_no_errorC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8in_stdinC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedc59OSSVerify5KrLib7Mh_00389StreamSim;init_M_loopC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9obs_tracec59OSSVerify5KrLib7Mh_00389StreamSim=stream_tracesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim>star_loop_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSimKstream_traces_prefix_closedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSimBstream_star_admitsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00c59OSSVerify5KrLib7Mh_00389StreamSim>to_rd_no_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00266SimInv:inv_coexecC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim<to_rd_coexecC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6coexec00K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:omni_corunC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=prefix_closedI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6cosafe00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun>cosafe_obs_iffc59OSSVerify5KrLib7Mh_00389StreamSim>stream_obs_iffC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;omni_cosafeC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<img_segmentsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7coveredC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence:omni_equivc59OSSVerify5KrLib7Mh_00389StreamSimAstream_omni_corunC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRunDnever_errors_coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=coexec_conseqC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun8omni_runC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence@omni_trace_equivC4ELinuxProcessSemantics?LinuxProcessSem3Run3runC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalenceDtrace_equiv_iff_omniC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6errorsI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence7modeledC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence5equivc59OSSVerify5KrLib7Mh_00389StreamSim?stream_no_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00266SimInvDno_error_run_modeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=bh_all_errorsC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errors".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_arg1_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma syscall_spec_read : forall segs ms x8 model o,
  bv_unsigned x8 = 63%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> read_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
         (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  change (in_sysno (sys_input segs ms x8)) with x8.
  rewrite Hno. reflexivity.
Qed.

Lemma in_arg2_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.

Lemma in_wmem_sys_input : forall segs ms x8,
  in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma band0_255 : bv_and (Z_to_bv 64 0) (Z_to_bv 64 255) = Z_to_bv 64 0.
Proof.
  apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_fs_with_stdin : forall s m, m_fs (with_stdin s m) = m_fs m.
Proof. reflexivity. Qed.

Lemma m_halted_with_stdin : forall s m, m_halted (with_stdin s m) = m_halted m.
Proof. reflexivity. Qed.

Lemma m_fds_with_stdin : forall s m, m_fds (with_stdin s m) = m_fds m.
Proof. reflexivity. Qed.

Lemma m_vm_lazy_with_stdin : forall s m,
  m_vm_lazy (with_stdin s m) = m_vm_lazy m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition M_loop (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
  fd1chan model /\
  m_halted model = None /\
  m_vm_lazy model = [].

Lemma init_M_loop : forall reserved brk0 mb sp lim inp,
  in_channel_reader inp = true ->
  M_loop (init_model reserved brk0 mb sp lim inp).
Proof.
  intros reserved brk0 mb sp lim inp Hr.
  split; [reflexivity | split; [apply init_model_fd1chan; exact Hr | split; reflexivity]].
Qed.

(* [comment removed for export] *)
Lemma M_loop_take : forall k model,
  M_loop model ->
  M_loop (with_stdin (snd (stream_take (m_stdin model) k)) model).
Proof.
  intros k model (H0 & H1 & Hh & Hlazy).
  split; [exact H0 | split; [exact H1 | split; assumption]].
Qed.

Lemma M_loop_fd1chan : forall model, M_loop model -> fd1chan model.
Proof. intros model (H0 & H1 & Hh & Hlazy). exact H1. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match find_segment segs (bv_unsigned a) 1 with
      | Some seg =>
          (seg_writable seg
           && match segment_byte_at (seg_bytes seg)
                      (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) with
              | Some _ => true
              | None => false
              end
           && wseg_ok segs (a + 1) n')%bool
      | None => false
      end
  end.

Lemma wseg_ok_read_aux : forall segs n a ms,
  wseg_ok segs a n = true ->
  exists w, read_bytes_aux (ms_writable_byte segs ms) a n = Some w.
Proof.
  intros segs n; induction n as [|n IH]; intros a ms H.
  - exists []. reflexivity.
  - cbn [wseg_ok] in H.
    destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
    apply andb_true_iff in H as [H Hrec].
    apply andb_true_iff in H as [Hwr Hbyte].
    destruct (segment_byte_at (seg_bytes seg)
                (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
      [|discriminate].
    destruct (IH (a + 1) ms Hrec) as [w Hw].
    cbn [read_bytes_aux].
    assert (Hdef : exists b0, ms_writable_byte segs ms a = Some b0).
    { unfold ms_writable_byte, wview. destruct (ms_mem ms a) as [b'|].
      - eexists; reflexivity.
      - rewrite Hseg, Hwr, Hb. eexists; reflexivity. }
    destruct Hdef as [b0 Hb0]. rewrite Hb0, Hw. eexists; reflexivity.
Qed.

Lemma wseg_ok_wdef : forall segs (a len : word) ms,
  wseg_ok segs a (word_to_nat len) = true ->
  exists w, read_bytes_map (ms_writable_byte segs ms) a len = Some w.
Proof.
  intros segs a len ms H. rewrite read_bytes_map_eq.
  apply wseg_ok_read_aux. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma read0_wmem1 : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 w,
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  exists w1, read_bytes_map (in_wmem (sys_input segs ms x8)) (ms_gpr ms 1)
               (Z_to_bv 64 1) = Some w1.
Proof.
  intros cnt Hcnt segs ms x8 w Hw. rewrite in_wmem_sys_input.
  eexists. apply (read_bytes_map_prefix _ _ cnt (Z_to_bv 64 1) w);
    [rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; lia | exact Hw].
Qed.

(* [comment removed for export] *)
Lemma read0_wmem_need : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 w s,
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  exists wn, read_bytes_map (in_wmem (sys_input segs ms x8)) (ms_gpr ms 1)
               (len_word (fst (stream_take_z s (rw_count_clamp cnt)))) = Some wn.
Proof.
  intros cnt Hcnt segs ms x8 w s Hw. rewrite in_wmem_sys_input.
  eexists. apply (read_bytes_map_prefix _ _ cnt _ w); [|exact Hw].
  rewrite stream_take_z_eq.
  pose proof (stream_take_length (Z.to_nat (rw_count_clamp cnt)) s) as Hlen.
  pose proof (rw_count_clamp_range cnt) as Hcl.
  unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap_small;
    unfold bv_modulus, MAX_RW_COUNT in *; cbn [Z.of_N] in *;
    [ | pose proof (bv_unsigned_in_range 64 cnt) ]; unfold rw_count_clamp in *; lia.
Qed.

Lemma read0_check_eof : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  m_stdin model = IEof ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  check_read (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (mkEffect (Z_to_bv 64 0) [] []) model
    = CheckOk model [].
Proof.
  intros cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok.
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  unfold check_read.
  rewrite Hg0; norm_fd32; rewrite Hfd.
  cbv beta iota.
  change (negb (w_is0 (Z_to_bv 64 0))) with false. cbv beta iota.
  rewrite Hg2, Haok.
  cbn [negb]. cbv beta iota. rewrite Hcnt0. cbv beta iota.
  rewrite Heof. cbv beta iota.
  unfold check_ret_only. rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma read0_check_bytes : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w bs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  check_read (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model
    = CheckOk (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
              (map (ReadEv (Z_to_bv 64 0)) bs).
Proof.
  intros cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre.
  destruct (read0_wmem1 cnt Hcnt segs ms x8 w Hw) as [w1 Hw1].
  destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw) as [wn Hwn].
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  unfold check_read.
  rewrite Hg0; norm_fd32; rewrite Hfd.
  cbv beta iota.
  change (negb (w_is0 (Z_to_bv 64 0))) with false. cbv beta iota.
  rewrite Hg2, Haok.
  cbn [negb]. cbv beta iota. rewrite Hcnt0. cbv beta iota.
  (* the input cannot have run out: a nonempty prefix was delivered *)
  destruct (m_stdin model) as [|b0 s0] eqn:Hs.
  { exfalso. rewrite stream_take_nil_of_eof in Hpre. subst bs. cbn in Hlo. lia. }
  cbv beta iota.
  rewrite Hw1. cbv beta iota.
  rewrite Hwn. cbv beta iota.
  rewrite !bv_eqb_refl.
  rewrite (proj2 (Z.leb_le 1 (Z.of_nat (length bs))) Hlo).
  rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)).
  rewrite (proj2 (Z.leb_le (Z.of_nat (length bs)) (bv_unsigned cnt)) Hhi).
  rewrite (proj2 (listN_eqb_eq _ _) Hpre).
  rewrite <- (in_wmem_sys_input segs ms x8) in Hw.
  assert (Hlek : (bv_unsigned (len_word bs) <= bv_unsigned cnt)%Z).
  { unfold len_word. pose proof (bv_unsigned_in_range 64 cnt) as Hr.
    rewrite Z_to_bv_unsigned, bv_wrap_small; [exact Hhi | lia]. }
  rewrite (wmem_ok_of_full _ _ _ _ _ Hw Hlek).
  reflexivity.
Qed.

Lemma read0_ok_eof : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  m_stdin model = IEof ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (Z_to_bv 64 0) [] []) model []).
Proof.
  intros cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok.
  apply (proj2 (syscall_spec_read _ _ _ _ _ Hno)).
  apply check_read_sound_ok. eapply read0_check_eof; eassumption.
Qed.

Lemma read0_ok_bytes : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w bs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
        (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
        (map (ReadEv (Z_to_bv 64 0)) bs)).
Proof.
  intros cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre.
  apply (proj2 (syscall_spec_read _ _ _ _ _ Hno)).
  apply check_read_sound_ok. eapply read0_check_bytes; eassumption.
Qed.

(* [comment removed for export] *)
Lemma read0_ok_inv : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model buf w eff model' evs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  (m_stdin model = IEof /\ eff = mkEffect (Z_to_bv 64 0) [] [] /\
   model' = model /\ evs = [])
  \/ (exists bs,
        (1 <= Z.of_nat (length bs))%Z /\
        (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
        fst (stream_take (m_stdin model) (length bs)) = bs /\
        eff = mkEffect (len_word bs) [(buf, bs)] [] /\
        model' = with_stdin (snd (stream_take (m_stdin model) (length bs))) model /\
        evs = map (ReadEv (Z_to_bv 64 0)) bs).
Proof.
  intros cnt Hcnt segs ms x8 model buf w eff model' evs
         Hno Hfd Hg0 Hg1 Hg2 Hw Haok Hspec.
  destruct (read0_wmem1 cnt Hcnt segs ms x8 w) as [w1 Hw1];
    [rewrite Hg1; exact Hw|].
  rewrite Hg1 in Hw1.
  destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model)) as [wn Hwn];
    [rewrite Hg1; exact Hw|].
  rewrite Hg1 in Hwn.
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  apply (proj1 (syscall_spec_read _ _ _ _ _ Hno)) in Hspec.
  apply check_read_complete_ok in Hspec.
  unfold check_read in Hspec.
  rewrite Hg0 in Hspec; norm_fd32; rewrite Hfd in Hspec.
  cbv beta iota in Hspec.
  change (negb (w_is0 (Z_to_bv 64 0))) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite Hg1, Hg2, Haok in Hspec.
  cbn [negb] in Hspec. cbv beta iota in Hspec. rewrite Hcnt0 in Hspec. cbv beta iota in Hspec.
  destruct (m_stdin model) as [|b0 s0] eqn:Hs; cbv beta iota in Hspec.
  - (* the input has run out *)
    apply check_ret_only_ok_iff in Hspec.
    destruct Hspec as (-> & -> & ->). left. auto.
  - (* bytes delivered from the head of the remaining input *)
    rewrite Hw1 in Hspec. cbv beta iota in Hspec.
    rewrite Hwn in Hspec. cbv beta iota in Hspec.
    destruct eff as [ret ws zs us cs copyins].
    destruct ws as [|[a bs] [|w2 ws]]; [discriminate| |discriminate].
    destruct zs as [|z zs]; [|discriminate].
    destruct us as [|u us]; [|discriminate].
    destruct cs as [|c cs]; [|discriminate].
    destruct copyins as [|copyin copyins]; [|discriminate].
    destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
              && (1 <=? Z.of_nat (length bs))%Z
              && (Z.of_nat (length bs) <=? rw_count_clamp cnt)%Z
              && listN_eqb (fst (stream_take (ICons b0 s0) (length bs))) bs
              && wmem_ok (sys_input segs ms x8) buf (len_word bs)) eqn:Hb;
      try rewrite Hb in Hspec; [|discriminate].
    inversion Hspec; subst.
    apply andb_true_iff in Hb as [Hb _].
    apply andb_true_iff in Hb as [Hb HE].
    apply andb_true_iff in Hb as [Hb HD].
    apply andb_true_iff in Hb as [Hb HC].
    apply andb_true_iff in Hb as [HA HB].
    apply bv_eqb_eq in HA; subst a.
    apply bv_eqb_eq in HB; subst ret.
    apply Z.leb_le in HC. apply Z.leb_le in HD.
    rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)) in HD.
    apply listN_eqb_eq in HE.
    right. exists bs. repeat split; try assumption; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma read0_no_unmodeled : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros cnt Hcnt segs ms x8 model w Hno Hfd Hg0 Hg2 Hw Haok Hspec.
  destruct (read0_wmem1 cnt Hcnt segs ms x8 w Hw) as [w1 Hw1].
  destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw) as [wn Hwn].
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  apply (proj1 (syscall_spec_read _ _ _ _ _ Hno)) in Hspec.
  apply (check_read_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_read in Hspec.
  rewrite Hg0 in Hspec; norm_fd32; rewrite Hfd in Hspec.
  cbv beta iota in Hspec.
  change (negb (w_is0 (Z_to_bv 64 0))) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite Hg2, Haok in Hspec.
  cbn [negb] in Hspec. cbv beta iota in Hspec. rewrite Hcnt0 in Hspec. cbv beta iota in Hspec.
  destruct (m_stdin model) as [|b0 s0] eqn:Hs; cbv beta iota in Hspec.
  { now apply check_ret_only_no_unmodeled in Hspec. }
  rewrite Hw1 in Hspec. cbv beta iota in Hspec.
  rewrite Hwn in Hspec. cbv beta iota in Hspec. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_read_inv : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms model buf x8 w evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true ->
  sstep segs (mkCfg ms model) evs st ->
  (m_stdin model = IEof /\ evs = [] /\
   st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model))
  \/ (exists bs,
        (1 <= Z.of_nat (length bs))%Z /\
        (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
        fst (stream_take (m_stdin model) (length bs)) = bs /\
        evs = map (ReadEv (Z_to_bv 64 0)) bs /\
        st = SNext (mkCfg
               (advance_past_svc (apply_effect ms
                  (mkEffect (len_word bs) [(buf, bs)] [])))
               (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                           model))).
Proof.
  intros cnt Hcnt segs ms model buf x8 w evs st
         Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(Hs & Heff & Hm & Hevs) | (bs & Hlo & Hhi & Hpre & Heff & Hm & Hevs)];
        subst eff model' evs0
    end.
    + match goal with
      | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
          rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
          inversion Hmat; subst model''
      end.
      left. rewrite apply_effect_no_write.
      split; [exact Hs | split; reflexivity].
    + match goal with
      | Hmat : materialize_model_accesses
                   (with_stdin ?s model) _ = Some ?model'' |- _ =>
          rewrite (materialize_model_accesses_no_lazy (with_stdin s model) _)
            in Hmat by (rewrite m_vm_lazy_with_stdin; exact Hlazy);
          inversion Hmat; subst model''
      end.
      right. exists bs. repeat split; try assumption; reflexivity.
  - (* sstep_syscall_materialization_fault: this loop has no lazy maps *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
      subst model';
      [ rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy
                   (with_stdin (snd (stream_take (m_stdin model) (length bs))) model) _)
          in Hmat by (rewrite m_vm_lazy_with_stdin; exact Hlazy) ];
      discriminate
    end.
  - (* sstep_exit: the read leaves the model un-halted *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
        subst model'; [|rewrite m_halted_with_stdin in H6]; congruence
    end.
  - (* sstep_killed: the read leaves the model unkilled, as it leaves it
       un-halted -- [State.m_killed_of_m_halted_none] on the pre-model *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
        subst model';
        [ rewrite (m_killed_of_m_halted_none model Hh) in H6
        | rewrite (m_killed_of_m_halted_none _
                     (eq_trans (m_halted_with_stdin _ model) Hh)) in H6 ];
        discriminate
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (read0_no_unmodeled _ Hcnt segs ms x8 model w Hno Hfd Hg0 eq_refl Hw
               Haok H3)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive chunks (cnt : word) : InputStream -> list (list byte) -> InputStream -> Prop :=
| chunks_nil : forall s, chunks cnt s [] s
| chunks_cons : forall s bs blocks s'',
    (1 <= Z.of_nat (length bs))%Z ->
    (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
    fst (stream_take s (length bs)) = bs ->
    chunks cnt (snd (stream_take s (length bs))) blocks s'' ->
    chunks cnt s (bs :: blocks) s''.

(* [comment removed for export] *)
Lemma chunks_app : forall cnt s l1 s1 l2 s2,
  chunks cnt s l1 s1 -> chunks cnt s1 l2 s2 -> chunks cnt s (l1 ++ l2) s2.
Proof.
  intros cnt s l1 s1 l2 s2 H1; revert l2 s2.
  induction H1 as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros l2 s2 H2; cbn [app]; [exact H2|].
  eapply chunks_cons; eauto.
Qed.

Lemma chunks_split : forall cnt l1 l2 s s2,
  chunks cnt s (l1 ++ l2) s2 ->
  exists s1, chunks cnt s l1 s1 /\ chunks cnt s1 l2 s2.
Proof.
  intros cnt l1; induction l1 as [|bs l1 IH]; intros l2 s s2 H; cbn [app] in H.
  - exists s. split; [constructor | exact H].
  - inversion H as [|s0 bs0 blocks0 s3 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
    destruct (IH l2 _ _ HC) as (s1 & H1 & H2).
    exists s1. split; [eapply chunks_cons; eauto | exact H2].
Qed.

(* [comment removed for export] *)
Lemma chunks_single_inv : forall cnt s bs s',
  chunks cnt s [bs] s' ->
  (1 <= Z.of_nat (length bs))%Z /\
  (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
  fst (stream_take s (length bs)) = bs /\
  s' = snd (stream_take s (length bs)).
Proof.
  intros cnt s bs s' H.
  inversion H as [|s0 bs0 blocks0 s2 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
  inversion HC; subst.
  repeat split; assumption || reflexivity.
Qed.

(* [comment removed for export] *)
Definition iter_ev_ch (rch : word) (bs : list byte) : list event :=
  map (ReadEv rch) bs ++ map (WriteEv (Z_to_bv 64 1)) bs.

(* [comment removed for export] *)
Definition iter_ev (bs : list byte) : list event :=
  iter_ev_ch (Z_to_bv 64 0) bs.

(* [comment removed for export] *)
Definition eof_tail (s : InputStream) (fs : Fs.Fs) : list event :=
  match s with
  | IEof => [ExitEv (Z_to_bv 64 0) fs]
  | ICons _ _ => []
  end.

(* [comment removed for export] *)
Definition stream_traces_ch (rch : word) (cnt : word) (fs : Fs.Fs)
    (s : InputStream) (tr : list event) : Prop :=
  exists blocks s',
    chunks cnt s blocks s' /\
    is_prefix tr (flat_map (iter_ev_ch rch) blocks ++ eof_tail s' fs).

(* [comment removed for export] *)
Definition stream_traces (cnt : word) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  stream_traces_ch (Z_to_bv 64 0) cnt fs s tr.

Lemma stream_traces_ch_prefix_closed : forall rch cnt fs s tr tr',
  stream_traces_ch rch cnt fs s tr -> is_prefix tr' tr ->
  stream_traces_ch rch cnt fs s tr'.
Proof.
  intros rch cnt fs s tr tr' (blocks & s' & HC & Hp) Hp'.
  exists blocks, s'. split; [exact HC | eapply is_prefix_trans; eauto].
Qed.

Lemma stream_traces_prefix_closed : forall cnt fs s tr tr',
  stream_traces cnt fs s tr -> is_prefix tr' tr -> stream_traces cnt fs s tr'.
Proof. exact (stream_traces_ch_prefix_closed (Z_to_bv 64 0)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Loop.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable LH : machine_state -> Prop.
Variable cnt : word.
(* [comment removed for export] *)
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.

(* [comment removed for export] *)
Definition lh_next (ms : machine_state) : Prop :=
  exists ms', msteps segs ms ms' /\ LH ms'.

(* [comment removed for export] *)
Definition WrPend (bs : list byte) (ms : machine_state) : Prop :=
  (1 <= length bs)%nat /\
  to_wall segs (Z_to_bv 64 1) ms bs lh_next.

(* [comment removed for export] *)
Inductive to_wr (bs : list byte) : machine_state -> Prop :=
| twr_here : forall ms, WrPend bs ms -> to_wr bs ms
| twr_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wr bs ms' -> to_wr bs ms.

(* [comment removed for export] *)
Definition ReadPend (ms : machine_state) : Prop :=
  exists buf x8,
  ms_svc_pending ms = Some x8 /\
  bv_unsigned x8 = 63%Z /\
  ms_gpr ms 0 = Z_to_bv 64 0 /\
  ms_gpr ms 1 = buf /\
  ms_gpr ms 2 = cnt /\
  (exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w) /\
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true /\
  to_exit segs (Z_to_bv 64 0) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
  (forall bs,
     (1 <= Z.of_nat (length bs))%Z ->
     (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
     to_wr bs (advance_past_svc (apply_effect ms
        (mkEffect (len_word bs) [(buf, bs)] [])))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma msteps_to_wr : forall bs ms ms',
  msteps segs ms ms' -> to_wr bs ms' -> to_wr bs ms.
Proof.
  intros bs ms ms' H; induction H; [auto|].
  intro Hwr. eapply twr_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma to_wr_wall_tail : forall bs ms,
  to_wr bs ms -> to_wall_tail segs (Z_to_bv 64 1) ms bs lh_next.
Proof.
  intros bs ms H; induction H as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
  - destruct HWP as [Hnb Hw]. apply twt_more; assumption.
  - eapply twt_step; eauto.
Qed.

Inductive to_rd : machine_state -> Prop :=
| trd_here : forall ms, ReadPend ms -> to_rd ms
| trd_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd ms' -> to_rd ms.

Lemma msteps_to_rd : forall ms ms',
  msteps segs ms ms' -> to_rd ms' -> to_rd ms.
Proof.
  intros ms ms' H; induction H; [auto|].
  intro Hrd. eapply trd_step; eauto.
Qed.

(* [comment removed for export] *)
Hypothesis H_LH : forall ms, LH ms -> to_rd ms.

Lemma lh_next_to_rd : forall ms, lh_next ms -> to_rd ms.
Proof.
  intros ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_rd_star : forall ms model,
  m_halted model = None -> m_vm_lazy model = [] -> to_rd ms ->
  exists msR, ReadPend msR /\
    star segs (mkCfg ms model) [] (mkCfg msR model).
Proof.
  intros ms model Hh Hlazy Hrd.
  induction Hrd as [ms HRP | ms ms' Hsvc Hstep Hrd IH].
  - exists ms. split; [exact HRP | apply star_refl].
  - destruct IH as (msR & HRP & Hstar).
    exists msR. split; [exact HRP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_wr_star : forall bs ms model,
  m_halted model = None -> m_vm_lazy model = [] -> to_wr bs ms ->
  exists msW, WrPend bs msW /\
    star segs (mkCfg ms model) [] (mkCfg msW model).
Proof.
  intros bs ms model Hh Hlazy Hwr.
  induction Hwr as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
  - exists ms. split; [exact HWP | apply star_refl].
  - destruct IH as (msW & HWP & Hstar).
    exists msW. split; [exact HWP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stream_star_admits : forall s blocks s',
  chunks cnt s blocks s' ->
  forall ms model,
  M_loop model -> m_stdin model = s -> to_rd ms ->
  exists c, star segs (mkCfg ms model)
              (flat_map iter_ev blocks ++ eof_tail s' (m_fs model)) c.
Proof.
  intros s blocks s' HC.
  induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros ms model HM Hst Hrd; pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  - (* no more blocks *)
    cbn [flat_map app].
    destruct s as [|b0 s0] eqn:Hs.
    + (* the input has run out: resolve the read as EOF, then exit(0) *)
      destruct (to_rd_star ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
      destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & _).
      destruct (to_exit_star_admits segs (Z_to_bv 64 0)
                  (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0))) model Hh Hlazy Hex)
        as [c Hstar2].
      exists c.
      assert (HssE : sstep segs (mkCfg msR model) []
                (SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0)))
                              model))).
      { rewrite <- (apply_effect_no_write msR (Z_to_bv 64 0)).
        apply (sstep_syscall segs msR model x8 (mkEffect (Z_to_bv 64 0) [] [])
                 model model []);
          [exact Hh | exact Hsvc | | exact Hh |].
        - rewrite <- Hg1 in Hw, Haok. eapply (read0_ok_eof cnt Hcnt); eassumption.
        - rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity. }
      cbn [eof_tail].
      replace [ExitEv (Z_to_bv 64 0) (m_fs model)]
        with (([] : list event)
                ++ ([] ++ [ExitEv (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255))
                             (m_fs model)]))
        by (rewrite band0_255; reflexivity).
      eapply star_trans; [exact Hstar0|].
      eapply star_step; [exact HssE | exact Hstar2].
    + (* input remains: the empty trace is a prefix of this run *)
      cbn [eof_tail app]. exists (mkCfg ms model). apply star_refl.
  - (* one more block: deliver it, echo ALL of it through the retry
       loop, loop *)
    destruct (to_rd_star ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
    pose proof (Hbytes bs Hlo Hhi) as Hwr.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bs) [(buf, bs)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bs))) model).
    assert (Hh' : m_halted model' = None) by exact Hh.
    assert (HM' : M_loop model')
      by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
              (SNext (mkCfg advB model'))).
    { apply (sstep_syscall segs msR model x8
               (mkEffect (len_word bs) [(buf, bs)] []) model' model'
               (map (ReadEv (Z_to_bv 64 0)) bs));
        [exact Hh | exact Hsvc | | exact Hh' |].
      - unfold model'. rewrite <- Hst. rewrite <- Hg1. rewrite <- Hg1 in Hw, Haok.
        eapply (read0_ok_bytes cnt Hcnt); try eassumption.
        rewrite Hst. exact Hpre.
      - rewrite (materialize_model_accesses_no_lazy model' _ (proj2 (proj2 (proj2 HM')))).
        reflexivity. }
    assert (Hfdc' : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model')
      by (apply fd1chan_fdchan; exact Hfd1).
    assert (Hbmbs : buf_modeled bs) by (unfold buf_modeled; lia).
    assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
      by reflexivity.
    assert (Hcont : forall ms', lh_next ms' ->
              exists c, star segs (mkCfg ms' model')
                (flat_map iter_ev blocks ++ eof_tail s'' (m_fs model')) c).
    { intros ms' Hlh.
      apply (IH ms' model' HM' Hst' (lh_next_to_rd ms' Hlh)). }
    destruct (to_wall_tail_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1)
                fd32_1 advB bs lh_next (to_wr_wall_tail bs advB Hwr) Hbmbs
                model' _ Hh' (proj2 (proj2 (proj2 HM'))) Hfdc' Hcont) as [c Hstar1].
    exists c.
    change (m_fs model') with (m_fs model) in Hstar1.
    cbn [flat_map]. unfold iter_ev at 1; unfold iter_ev_ch.
    rewrite <- !app_assoc.
    replace (map (ReadEv (Z_to_bv 64 0)) bs
               ++ map (WriteEv (Z_to_bv 64 1)) bs
               ++ flat_map iter_ev blocks ++ eof_tail s'' (m_fs model))
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bs
                    ++ (map (WriteEv (Z_to_bv 64 1)) bs
                          ++ (flat_map iter_ev blocks
                                ++ eof_tail s'' (m_fs model)))))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma star_loop_only : forall c0 tr c', star segs c0 tr c' ->
  forall ms model, c0 = mkCfg ms model -> M_loop model ->
  (to_rd ms ->
     exists blocks s', chunks cnt (m_stdin model) blocks s' /\
       is_prefix tr (flat_map iter_ev blocks ++ eof_tail s' (m_fs model)))
  /\ (forall bs, (1 <= length bs)%nat -> buf_modeled bs ->
     to_wall_tail segs (Z_to_bv 64 1) ms bs lh_next ->
     exists blocks s',
       chunks cnt (m_stdin model) blocks s' /\
       is_prefix tr (map (WriteEv (Z_to_bv 64 1)) bs
                       ++ flat_map iter_ev blocks
                       ++ eof_tail s' (m_fs model))).
Proof.
  intros c0 tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH];
    intros ms model Heq HM; subst.
  - (* star_refl: the empty trace *)
    split.
    + intros _. exists [], (m_stdin model).
      split; [constructor | apply is_prefix_nil].
    + intros bs _ _ _. exists [], (m_stdin model).
      split; [constructor | apply is_prefix_nil].
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    split.
    + (* phase A: on the way to / at the read *)
      intro Hrd. destruct Hrd as [ms (buf & x8 & HRP) | ms ms' Hsvc Hstep Hrd'].
      * (* at the read ecall *)
        destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
        destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs (SNext c2)
                    Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
          as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
          inversion Hc2; subst.
        -- (* end of input: the rest of the run is the exit tail *)
           destruct (to_exit_star_only segs (Z_to_bv 64 0)
                       (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model
                       Hh Hlazy Hex tr2 c3 Hstar) as [-> | ->].
           ++ exists [], (m_stdin model).
              split; [constructor | apply is_prefix_nil].
           ++ exists [], (m_stdin model).
              split; [constructor|].
              rewrite Hs, band0_255. cbn [flat_map app eof_tail].
              apply is_prefix_refl.
        -- (* bytes: the rest of the run is a write-all phase *)
           assert (Hnb : (1 <= length bs)%nat) by lia.
           assert (Hbmbs : buf_modeled bs) by (unfold buf_modeled; lia).
           destruct (proj2 (IH _ _ eq_refl (M_loop_take (length bs) model HM)) bs
                       Hnb Hbmbs (to_wr_wall_tail bs _ (Hbytes bs Hlo Hhi)))
             as (blocks & s' & HCb & Hp).
           exists (bs :: blocks), s'.
           split; [eapply chunks_cons; eassumption|].
           cbn [flat_map]. unfold iter_ev at 1; unfold iter_ev_ch.
           rewrite <- !app_assoc.
           apply is_prefix_app_mono. exact Hp.
      * (* an ordinary instruction *)
        destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                    Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
        inversion Hc2; subst.
        exact (proj1 (IH _ model eq_refl HM) Hrd').
    + (* phase B: inside the echo write-all (retry) loop *)
      intros bs Hnb Hbm Hwt.
      inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl | msS msS' restS kS HsvcS HstepS Hwt']; subst.
      * (* twt_done: the remainder is [], contradicting nonemptiness *)
        cbn in Hnb. lia.
      * (* twt_more: at the write ecall *)
        destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                    ms bs lh_next model evs (SNext c2) Hh Hlazy Hfdc Hbm Hwl Hss)
          as (n & Hn1 & Hn2 & Hevs & Hc2 & Hwt2).
        inversion Hc2; subst.
        set (adv := advance_past_svc (set_gpr0 ms (len_word (firstn n bs)))) in *.
        destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
        -- (* full delivery: the remainder is empty; back to the read *)
           rewrite skipn_all in Hwt2.
           destruct (to_wall_tail_nil_msteps segs (Z_to_bv 64 1) adv lh_next Hwt2)
             as (msL & HmL & HlhL).
           destruct (proj1 (IH _ model eq_refl HM)
                       (msteps_to_rd adv msL HmL (lh_next_to_rd msL HlhL)))
             as (blocks & s' & HCb & Hp).
           exists blocks, s'. split; [exact HCb|].
           rewrite firstn_all.
           apply is_prefix_app_mono. exact Hp.
        -- (* short delivery: the remainder is a shorter write-all phase *)
           assert (Hnb' : (1 <= length (skipn n bs))%nat)
             by (rewrite length_skipn; lia).
           destruct (proj2 (IH _ model eq_refl HM) (skipn n bs) Hnb'
                       (buf_modeled_skipn n bs Hbm) Hwt2)
             as (blocks & s' & HCb & Hp).
           exists blocks, s'. split; [exact HCb|].
           rewrite <- (firstn_skipn n bs) at 2.
           rewrite map_app, <- app_assoc.
           apply is_prefix_app_mono. exact Hp.
      * (* twt_step: an ordinary instruction *)
        destruct (sstep_instr_inv segs ms model msS' evs (SNext c2)
                    Hlazy HsvcS HstepS Hss) as [Hevs Hc2].
        inversion Hc2; subst.
        exact (proj2 (IH _ model eq_refl HM) bs Hnb Hbm Hwt').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sinv (c : config) : Prop :=
  (M_loop (cfg_model c) /\
     (to_rd (cfg_ms c)
      \/ exists bs, (1 <= length bs)%nat /\ buf_modeled bs /\
           to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) bs lh_next))
  \/ on_path segs (Z_to_bv 64 0) c.

Lemma sinv_step : forall c evs c',
  sinv c -> sstep segs c evs (SNext c') -> sinv c'.
Proof.
  intros [ms model] evs [ms' model'] Hinv Hss.
  destruct Hinv as [[HM Hphase] | Hop]; cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    destruct Hphase as [Hrd | (bs & Hnb & Hbm & Hwt)].
    + destruct Hrd as [ms (buf & x8 & HRP) | ms ms1 Hsvc Hstep Hrd'].
      * destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
        destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs
                    (SNext (mkCfg ms' model'))
                    Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
          as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
          inversion Hc2; subst.
        -- right. left. cbn. split; [exact Hh|].
           split; [exact Hlazy | exact Hex].
        -- left. cbn. split; [apply M_loop_take; exact HM|].
           right. exists bs. split; [lia|].
           split; [unfold buf_modeled; lia|].
           exact (to_wr_wall_tail bs _ (Hbytes bs Hlo Hhi)).
      * destruct (sstep_instr_inv segs ms model ms1 evs
                    (SNext (mkCfg ms' model')) Hlazy Hsvc Hstep Hss) as [_ Hc2].
        inversion Hc2; subst.
        left. cbn. split; [exact HM | left; exact Hrd'].
    + inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl
                       | msS msS' restS kS HsvcS HstepS Hwt']; subst.
      * (* twt_done: the remainder is [], contradicting nonemptiness *)
        cbn in Hnb. lia.
      * (* at the write ecall *)
        destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                    ms bs lh_next model evs (SNext (mkCfg ms' model'))
                    Hh Hlazy Hfdc Hbm Hwl Hss)
          as (n & Hn1 & Hn2 & _ & Hc2 & Hwt2).
        inversion Hc2; subst.
        set (adv := advance_past_svc (set_gpr0 ms (len_word (firstn n bs)))) in *.
        destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
        -- (* full delivery: back to the read phase *)
           rewrite skipn_all in Hwt2.
           destruct (to_wall_tail_nil_msteps segs (Z_to_bv 64 1) adv lh_next Hwt2)
             as (msL & HmL & HlhL).
           left. cbn. split; [exact HM|].
           left. exact (msteps_to_rd adv msL HmL (lh_next_to_rd msL HlhL)).
        -- (* short delivery: a shorter write-all phase *)
           left. cbn. split; [exact HM|].
           right. exists (skipn n bs).
           split; [rewrite length_skipn; lia|].
           split; [apply buf_modeled_skipn; exact Hbm | exact Hwt2].
      * destruct (sstep_instr_inv segs ms model msS' evs
                    (SNext (mkCfg ms' model')) Hlazy HsvcS HstepS Hss) as [_ Hc2].
        inversion Hc2; subst.
        left. cbn. split; [exact HM|].
        right. exists bs.
        split; [exact Hnb | split; [exact Hbm | exact Hwt']].
  - right. eapply on_path_step; eauto.
Qed.

Lemma sinv_no_error : forall c evs, sinv c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hinv Hss.
  destruct Hinv as [[HM Hphase] | Hop]; cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    destruct Hphase as [Hrd | (bs & Hnb & Hbm & Hwt)].
    + destruct Hrd as [ms (buf & x8 & HRP) | ms ms1 Hsvc Hstep Hrd'].
      * destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
        destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs SError
                    Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
          as [(_ & _ & Hc2) | (bs & _ & _ & _ & _ & Hc2)]; discriminate.
      * destruct (sstep_instr_inv segs ms model ms1 evs SError
                    Hlazy Hsvc Hstep Hss) as [_ Hc2]. discriminate.
    + inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl
                       | msS msS' restS kS HsvcS HstepS Hwt']; subst.
      * cbn in Hnb. lia.
      * exact (to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                 ms bs lh_next model evs Hh Hlazy Hfdc Hbm Hwl Hss).
      * destruct (sstep_instr_inv segs ms model msS' evs SError
                    Hlazy HsvcS HstepS Hss) as [_ Hc2]. discriminate.
  - eapply on_path_no_error; eauto.
Qed.

Lemma star_sinv : forall c tr c', sinv c -> star segs c tr c' -> sinv c'.
Proof. exact (star_inv segs sinv sinv_step). Qed.

Lemma to_rd_no_error : forall ms model,
  M_loop model -> to_rd ms -> ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model HM Hrd.
  apply (inv_no_reaches_error segs sinv sinv_step sinv_no_error).
  left; cbn; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stream_obs_iff : forall pc ph sp brk0 mb rnd lim inp,
  to_rd (init_machine_state segs pc ph sp mb rnd inp) ->
  in_channel_reader inp = true ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> stream_traces cnt (in_fs inp) (in_stdin inp) tr.
Proof.
  intros pc ph sp brk0 mb rnd lim inp Hrd Hrdr tr.
  set (fs0 := in_fs inp) in *; set (stdin0 := in_stdin inp) in *.
  unfold init_config.
  set (ms0 := init_machine_state segs pc ph sp mb rnd inp) in *.
  pose proof (init_M_loop (segments_reserved segs) brk0 mb sp lim inp Hrdr) as HM0'.
  set (model0 := with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                   (init_model (segments_reserved segs) brk0 mb sp lim inp)) in *.
  assert (HM0 : M_loop model0) by exact HM0'.
  assert (Hst0 : m_stdin model0 = stdin0) by reflexivity.
  assert (Hfs0 : m_fs model0 = fs0) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (proj1 (star_loop_only _ _ _ Hstar ms0 model0 eq_refl HM0) Hrd)
      as (blocks & s' & HC & Hp').
    rewrite Hst0 in HC. rewrite Hfs0 in Hp'.
    apply (stream_traces_prefix_closed cnt fs0 stdin0 tr'); [|exact Hp].
    exists blocks, s'. split; assumption.
  - intros (blocks & s' & HC & Hp).
    destruct (stream_star_admits stdin0 blocks s' HC ms0 model0 HM0 Hst0 Hrd)
      as [c Hstar].
    rewrite Hfs0 in Hstar.
    exists (flat_map iter_ev blocks ++ eof_tail s' fs0), c.
    split; assumption.
Qed.

Lemma stream_no_error : forall pc ph sp brk0 mb rnd lim inp,
  to_rd (init_machine_state segs pc ph sp mb rnd inp) ->
  in_channel_reader inp = true ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
  intros pc ph sp brk0 mb rnd lim inp Hrd Hrdr.
  apply to_rd_no_error; [apply init_M_loop; exact Hrdr | exact Hrd].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_rd_coexec : forall ms model,
  M_loop model -> to_rd ms -> OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof.
  intros ms model HM Hrd.
  apply (inv_coexec segs sinv sinv_step sinv_no_error). left; cbn; auto.
Qed.

Lemma stream_omni_corun : forall pc ph sp brk0 mb rnd lim inp,
  to_rd (init_machine_state segs pc ph sp mb rnd inp) ->
  in_channel_reader inp = true ->
  OmniRun.coexec segs (init_config segs pc ph sp brk0 mb rnd lim inp) never_errors.
Proof.
  intros pc ph sp brk0 mb rnd lim inp Hrd Hrdr. unfold init_config.
  set (model0 := with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                   (init_model (segments_reserved segs) brk0 mb sp lim inp)) in *.
  assert (HM0 : M_loop model0)
    by exact (init_M_loop (segments_reserved segs) brk0 mb sp lim inp Hrdr).
  apply to_rd_coexec; [exact HM0 | exact Hrd].
Qed.

Lemma stream_omni_cosafe : forall pc ph sp brk0 mb rnd lim inp,
  to_rd (init_machine_state segs pc ph sp mb rnd inp) ->
  in_channel_reader inp = true ->
  OmniRun.cosafe segs (init_config segs pc ph sp brk0 mb rnd lim inp)
    (stream_traces cnt (in_fs inp) (in_stdin inp)).
Proof.
  intros pc ph sp brk0 mb rnd lim inp Hrd Hrdr.
  apply cosafe_obs_iff.
  - intros t t' Ht Hp. eapply stream_traces_prefix_closed; eauto.
  - intros tr Hobs. apply (stream_obs_iff pc ph sp brk0 mb rnd lim inp Hrd Hrdr). exact Hobs.
Qed.

End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stream_omni_strong_equiv :
  forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd inp,
  (forall ms, rLH ms -> to_rd (run_segments source_segs inp rsp rmb) rLH cnt ms) ->
  (forall ms, aLH ms -> to_rd (run_segments target_segs inp asp amb) aLH cnt ms) ->
  to_rd (run_segments source_segs inp rsp rmb) rLH cnt
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) ->
  to_rd (run_segments target_segs inp asp amb) aLH cnt
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) ->
  in_channel_reader inp = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd
         inp HrLH HaLH Hr Ha Hrdr.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [exact (stream_omni_corun (run_segments source_segs inp rsp rmb) rLH cnt Hcnt HrLH
                rpc rph rsp rbrk rmb rrnd
                source_alloc_limit inp Hr Hrdr) | apply never_errors_covered]. }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (stream_obs_iff (run_segments source_segs inp rsp rmb) rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd source_alloc_limit inp Hr Hrdr tr).
    rewrite (stream_obs_iff (run_segments target_segs inp asp amb) aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha Hrdr tr).
    reflexivity.
  - exact (stream_omni_corun (run_segments target_segs inp asp amb) aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha Hrdr).
Qed.

Lemma stream_strong_equiv :
  forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim inp,
  (forall ms, rLH ms -> to_rd (run_segments source_segs inp rsp rmb) rLH cnt ms) ->
  (forall ms, aLH ms -> to_rd (run_segments target_segs inp asp amb) aLH cnt ms) ->
  to_rd (run_segments source_segs inp rsp rmb) rLH cnt
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) ->
  to_rd (run_segments target_segs inp asp amb) aLH cnt
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) ->
  in_channel_reader inp = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim
         inp HrLH HaLH Hr Ha Hrdr.
  split.
  { apply no_error_run_modeled.
    apply (stream_no_error (run_segments source_segs inp rsp rmb) rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr Hrdr). }
  right. split.
  - intro tr. cbn.
    rewrite (stream_obs_iff (run_segments source_segs inp rsp rmb) rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr Hrdr tr).
    rewrite (stream_obs_iff (run_segments target_segs inp asp amb) aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha Hrdr tr).
    reflexivity.
  - cbn. apply (stream_no_error (run_segments target_segs inp asp amb) aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha Hrdr).
Qed.

End StreamSim.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Mm.Mmap.
Module AllocSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WallSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_AllocSim () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsCeq_rewrite_relationI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes;EquivalenceEpointwise_equivalenceC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:Proper_mapc59OSSVerify5KrLib7Mh_00387CatExec=flat_map_app'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00387CatExec9skipn_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_00387CatExec>flat_map_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00387WallSim:u_len_wordC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions7bv_wrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6moduloC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z7add_0_rI47Corelib7Numbers7BinNums1N00C45stdpp9bitvector;definitions6bv_subC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC45stdpp9bitvector;definitions?bv_sub_unsignedK46Stdlib9micromega=RingMicromega3Op201C47Corelib4Init5Logic3notK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC45stdpp9bitvector;definitions@Z_to_bv_unsignedC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosc59OSSVerify5KrLib7Mh_00388AllocSim4zmemC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbK47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool;orb_false_rC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7existsbC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z6ltb_geK47Corelib7Numbers7BinNums8positive01C46Stdlib4Bool4Bool<andb_false_rc59OSSVerify5KrLib7Mh_00388AllocSim8zmem_outC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6leb_lec59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSim<word_add_0_rC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc59OSSVerify5KrLib7Mh_00388AllocSim>word_add_nat_SC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00306CatSim7fd1chanC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@forget_vm_rangesC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC46Stdlib5Lists4List6filterK4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC47Corelib7Classes?RelationClasses;reflexivityI4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome00C5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch:lookup_armC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7sa_specC4ELinuxProcessSemantics?LinuxProcessSem5Monad9unmodeledC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap8brk_specC47Corelib4Init5Logic3iffC4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoc59OSSVerify5KrLib7Mh_00388AllocSimEin_sysno_sys_input214C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specI4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7SpecArm00C5ELinuxProcessSemantics?LinuxProcessSem3Sys<SyscallTable:spec_tableC47Corelib7Classes?RelationClasses=iff_ReflexiveC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_unmapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>brk_model_nextc59OSSVerify5KrLib7Mh_00388AllocSimCfd1chan_with_vmmapsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSimHfd1chan_forget_vm_rangesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSim9brk_modelC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap9check_brkK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap8brk_r_okc59OSSVerify5KrLib7Mh_00388AllocSimAbrk_resolution_okC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=listNN_eqb_eqC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap9brk_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>brk_page_rangeC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=with_brk_nextK47Corelib4Init5Logic3and01I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init9Datatypes:comparison00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc59OSSVerify5KrLib7Mh_00388AllocSim@syscall_spec_brkC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapEcheck_brk_complete_okc59OSSVerify5KrLib7Mh_00388AllocSim@check_brk_ok_invC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc59OSSVerify5KrLib7Mh_00388AllocSimBcheck_brk_ok_introC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapBcheck_brk_sound_okK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01c59OSSVerify5KrLib7Mh_00388AllocSim:brk_ok_iffC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapLcheck_brk_complete_unmodeledK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03I47Corelib4Init5Logic2ex00C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap7min_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;brk_grow_okC49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool:orb_true_rC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=brk_budget_okC56Stdlib6ZArith6BinInt1Z:ltb_irreflC46Stdlib4Bool4Bool;andb_true_lc59OSSVerify5KrLib7Mh_00388AllocSim<brk_ok_introC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC47Corelib4Init9Datatypes4negbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_grantsc59OSSVerify5KrLib7Mh_00388AllocSim?brk_unmaps_keepC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapDpage_round_up_Z_monoc59OSSVerify5KrLib7Mh_00388AllocSim8vm_modelC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>vm_backed_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State7mkModelC4ELinuxProcessSemantics?LinuxProcessSem5StateAmaps_subtract_allC56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backed_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitc59OSSVerify5KrLib7Mh_00388AllocSim;brk_grow_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream01K4ELinuxProcessSemantics?LinuxProcessSem5State7FdState01K4ELinuxProcessSemantics?LinuxProcessSem5State7IoState01K4ELinuxProcessSemantics?LinuxProcessSem5State7FsState01K4ELinuxProcessSemantics?LinuxProcessSem5State8LimState01K4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState01C4ELinuxProcessSemantics?LinuxProcessSem5State9vmst_mapsK4ELinuxProcessSemantics?LinuxProcessSem5State5Creds01K4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState01C4ELinuxProcessSemantics?LinuxProcessSem5State;overflow_idC4ELinuxProcessSemantics?LinuxProcessSem5State:net_silentC4ELinuxProcessSemantics?LinuxProcessSem5State>default_nofileC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z7div_addK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula03c59OSSVerify5KrLib7Mh_00388AllocSimDround8_le_page_roundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z<eq_decidableK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02C46Stdlib4Bool4Bool=andb_true_iffC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC46Stdlib4Bool4Bool=negb_true_iffC46Stdlib4Bool4Bool>andb_false_iffK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c59OSSVerify5KrLib7Mh_00388AllocSimFpage_round_up_Z_boundsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedc59OSSVerify5KrLib7Mh_00388AllocSimGpage_round_up_Z_alignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSim@brk_grow_ok_growC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSim>brk_zeros_growC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_Nc59OSSVerify5KrLib7Mh_00388AllocSimBregion_free_prefixC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqc59OSSVerify5KrLib7Mh_00388AllocSim8brk_r_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<reserved_topK47Corelib5Lists7ListDef6Forall01C56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z3maxK47Corelib5Lists7ListDef6Forall02c59OSSVerify5KrLib7Mh_00388AllocSimEregion_free_above_topC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapDmaps_subtract_rangesc59OSSVerify5KrLib7Mh_00388AllocSim@brk_grants_queryC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSimDbrk_model_next_queryC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC46Stdlib4Bool4Bool<orb_true_iffC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes?RelationClasses>iff_TransitiveC46Stdlib5Lists4List9app_nil_rc59OSSVerify5KrLib7Mh_00388AllocSimBword_neq0_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSim;u_add_smallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSimAbrk_r_ok_grow_iffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSim2T1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSim8growableC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSim2T2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSim@brk_grow_ok_keepC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7add_0_lc59OSSVerify5KrLib7Mh_00388AllocSimCword_add_sub_cancelC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC47Corelib4Init9Datatypes8prod_indI59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00388AllocSim;to_outcomes00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01k59OSSVerify5KrLib7Mh_00388AllocSim;to_outcomes02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:msteps_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSimFforget_vm_ranges_frameC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesc59OSSVerify5KrLib7Mh_00388AllocSim>brk_step_shapeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04C4ELinuxProcessSemantics?LinuxProcessSem5StateIm_killed_of_m_halted_nonec59OSSVerify5KrLib7Mh_00388AllocSim@brk_no_unmodeledC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02c59OSSVerify5KrLib7Mh_00388AllocSim=outcomes_postC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec00c59OSSVerify5KrLib7Mh_00387WallSim;to_wallexitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<bufs_modeledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:wevents_chC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exits_withC59OSSVerify5KrLib7Mh_00306CatSim>fd1chan_fdchanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSim@to_wallexit_execC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim7weventsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSim>wevents_ch_fd1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_conseqC4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01C59OSSVerify5KrLib7Mh_00307ExitSim?sstep_instr_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun>exec_step_onlyc59OSSVerify5KrLib7Mh_00388AllocSim=brk_receptiveC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04c59OSSVerify5KrLib7Mh_00388AllocSim=sstep_brk_invC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome02c59OSSVerify5KrLib7Mh_00388AllocSim=outcome_traceC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec02c59OSSVerify5KrLib7Mh_00388AllocSim?to_outcomes_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome00c59OSSVerify5KrLib7Mh_00387WallSim6fd32_1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSim@to_outcomes_execC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_realizesI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun5mexec00K4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exec_soundC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6cosafe00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun?mexec_halt_starI4ELinuxProcessSemantics?LinuxProcessSem3Run4star00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;cosafe_starC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun9exec_starc59OSSVerify5KrLib7Mh_00387WallSimGto_wallexit_star_admitsC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run4star02C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunGexits_with_never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_no_errork59OSSVerify5KrLib7Mh_00388AllocSim;to_outcomes03C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00388AllocSim;to_outcomes01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun8omni_runI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C4ELinuxProcessSemantics?LinuxProcessSem3Run9obs_tracec59OSSVerify5KrLib7Mh_00388AllocSimEto_outcomes_star_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSimGto_outcomes_star_admitsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388AllocSim>alloc_omni_runC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?Equivalence_PERC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<img_segmentsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:omni_corunC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence:omni_equivC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_coexecC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunDnever_errors_coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=coexec_conseqC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence@omni_trace_equivC4ELinuxProcessSemantics?LinuxProcessSem3Run3runC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalenceDtrace_equiv_iff_omnic59OSSVerify5KrLib7Mh_00388AllocSim=alloc_obs_iffC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=bh_errors_iffc59OSSVerify5KrLib7Mh_00388AllocSimBalloc_no_error_runC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6errorsI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C47Corelib7Classes?RelationClasses?iff_equivalenceC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence7modeledC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence5equivC59OSSVerify5KrLib7Mh_00266SimInvDno_error_run_modeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=bh_all_errors".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u_add_small : forall a b : word,
  (bv_unsigned a + bv_unsigned b < 2 ^ 64)%Z ->
  bv_unsigned (a + b) = (bv_unsigned a + bv_unsigned b)%Z.
Proof.
  intros a b H. rewrite bv_add_unsigned, bv_wrap64_mod. apply Z.mod_small.
  pose proof (u64_range a). pose proof (u64_range b). lia.
Qed.

Lemma word_add_0_r : forall a : word, a + Z_to_bv 64 0 = a.
Proof.
  intro a. apply bv_eq.
  rewrite bv_add_unsigned.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r, bv_wrap64_mod. apply Z.mod_small. apply u64_range.
Qed.

(* [comment removed for export] *)
Lemma word_add_sub_cancel : forall r t : word, r + t - r = t.
Proof.
  intros r t. apply bv_eq.
  rewrite bv_sub_unsigned, bv_add_unsigned, !bv_wrap64_mod.
  rewrite Zminus_mod_idemp_l.
  replace (bv_unsigned r + bv_unsigned t - bv_unsigned r)%Z
    with (bv_unsigned t) by lia.
  apply Z.mod_small. apply u64_range.
Qed.

Lemma word_neq0_unsigned : forall r : word,
  r <> Z_to_bv 64 0 -> (bv_unsigned r <> 0)%Z.
Proof.
  intros r Hne Hu. apply Hne. apply bv_eq. rewrite Hu. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma word_add_nat_S : forall (a : word) k,
  (a + 1) + nat_to_word k = a + nat_to_word (S k).
Proof.
  intros a k. apply bv_eq. unfold nat_to_word.
  rewrite !bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change (bv_unsigned (1 : word)) with 1%Z.
  rewrite Zplus_mod_idemp_l, !Zplus_mod_idemp_r.
  f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zmem (mem : word -> option byte) (b l : word) : word -> option byte :=
  fun a => if Z.leb (bv_unsigned b) (bv_unsigned a)
              && Z.ltb (bv_unsigned a) (bv_unsigned b + bv_unsigned l)
           then Some (Z_to_bv 8 0) else mem a.

Lemma apply_zeros_nil : forall mem, apply_zeros mem [] = mem.
Proof. reflexivity. Qed.

Lemma apply_zeros_one : forall mem b l,
  apply_zeros mem [(b, l)] = zmem mem b l.
Proof.
  intros mem b l. apply functional_extensionality. intro a.
  unfold apply_zeros, zeros_cover, zmem. cbn [existsb fst snd].
  rewrite orb_false_r. reflexivity.
Qed.

Lemma zmem_out : forall mem b l a,
  (bv_unsigned a < bv_unsigned b \/ bv_unsigned b + bv_unsigned l <= bv_unsigned a)%Z ->
  zmem mem b l a = mem a.
Proof.
  intros mem b l a Hd. unfold zmem.
  destruct Hd as [Hd | Hd].
  - assert (E : (bv_unsigned b <=? bv_unsigned a)%Z = false) by (apply Z.leb_gt; lia).
    rewrite E. reflexivity.
  - assert (E : (bv_unsigned a <? bv_unsigned b + bv_unsigned l)%Z = false)
      by (apply Z.ltb_ge; lia).
    rewrite E, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_zmem_out : forall segs mem b l (a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned a + Z.of_nat n <= bv_unsigned b
   \/ bv_unsigned b + bv_unsigned l <= bv_unsigned a)%Z ->
  rdn segs (zmem mem b l) a n = rdn segs mem a n.
Proof.
  intros segs mem b l a n Hnw Hd. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply zmem_out. lia.
Qed.

Lemma rdn_zmem_in1 : forall segs mem b l (a : word),
  (bv_unsigned b <= bv_unsigned a < bv_unsigned b + bv_unsigned l)%Z ->
  rdn segs (zmem mem b l) a 1 = Some [Z_to_bv 8 0].
Proof.
  intros segs mem b l a [Hlo Hhi]. cbn [rdn]. unfold zmem.
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wbytes_app : forall {bs1 bs2 : list byte} m (a : word),
  wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (a + nat_to_word (length bs1)) bs2.
Proof.
  induction bs1 as [|b bs1 IH]; intros bs2 m a.
  - cbn [app wbytes length].
    replace (a + nat_to_word 0) with a; [reflexivity|].
    symmetry. exact (word_add_0_r a).
  - cbn [app wbytes length].
    rewrite IH, word_add_nat_S. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_vmmaps_fds : forall h m, m_fds (with_vmmaps h m) = m_fds m.
Proof. reflexivity. Qed.
Lemma with_vmmaps_fs : forall h m, m_fs (with_vmmaps h m) = m_fs m.
Proof. reflexivity. Qed.
Lemma with_vmmaps_halted : forall h m, m_halted (with_vmmaps h m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_vmmaps_vm : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. reflexivity. Qed.
Lemma with_vmmaps_lazy : forall h m,
  m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. reflexivity. Qed.

Lemma fd1chan_with_vmmaps : forall h m, fd1chan m -> fd1chan (with_vmmaps h m).
Proof. intros h m H. unfold fd1chan in *. exact H. Qed.

(* [comment removed for export] *)
Lemma fd1chan_forget_vm_ranges : forall ranges m,
  fd1chan m -> fd1chan (forget_vm_ranges ranges m).
Proof.
  induction ranges as [|[a n] ranges IH]; intros m H; cbn [forget_vm_ranges].
  - exact H.
  - apply IH. unfold fd1chan, vm_forget_range, with_vm_backing in *.
    cbn [m_fds m_fd] in *. exact H.
Qed.

(* [comment removed for export] *)
Lemma adv_brk : forall regs pc x8 mem rom r zs,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some x8;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} (mkEffect r [] zs))
  = mkst (regupd regs 10 r) (v_addi pc 4) (apply_zeros mem zs) rom.
Proof.
  intros regs pc x8 mem rom r zs.
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros apply_writes].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_sys_input214 : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Lemma in_arg0_sys_input214 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma syscall_spec_brk : forall segs ms x8 model o,
  bv_unsigned x8 = 214%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> brk_spec (ms_gpr ms 0) (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno. unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input214, Hno. reflexivity.
Qed.

(* [comment removed for export] *)
Definition vm_model (h : VmMaps) : Model :=
  mkModel [] h IEof [] None None None.

Definition brk_grow_ok (h : VmMaps) (req r : word) : bool :=
  Mmap.brk_grow_ok (vm_model h) req r.

(* [comment removed for export] *)
Definition brk_r_ok (h : VmMaps) (req r : word) : Prop :=
  Mmap.brk_r_ok (vm_model h) req r = true.

(* [comment removed for export] *)
Definition brk_resolution_ok (m : Model) (req r : word) : Prop :=
  Mmap.brk_r_ok m req r = true.

(* [comment removed for export] *)
Definition brk_model (req r : word) (m : Model) : Model :=
  with_brk_next m req r.

(* [comment removed for export] *)
Lemma fd1chan_brk_model : forall req r m,
  fd1chan m -> fd1chan (brk_model req r m).
Proof.
  intros req r m H. unfold brk_model, with_brk_next. cbv zeta.
  apply fd1chan_forget_vm_ranges, fd1chan_with_vmmaps, H.
Qed.

Lemma check_brk_ok_inv : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs ->
  eff = mkEffectU (eff_ret eff) []
          (brk_zeros req (eff_ret eff) (vm_brk (m_vmmaps m)))
          (brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps m))) [] []
  /\ evs = []
  /\ brk_resolution_ok m req (eff_ret eff)
  /\ m' = brk_model req (eff_ret eff) m.
Proof.
  intros req [r ws zs us cs copyins] m m' evs H.
  unfold check_brk in H.
  destruct ws as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (Mmap.brk_r_ok m req r) eqn:HR; [|cbn [andb] in H; discriminate].
  destruct (listNN_eqb zs (brk_zeros req r (vm_brk (m_vmmaps m)))) eqn:HZ;
    [|cbn [andb] in H; discriminate].
  destruct (listNN_eqb us (brk_unmaps r (vm_brk (m_vmmaps m)))) eqn:HU;
    [|cbn [andb] in H; discriminate].
  cbn [andb] in H.
  apply listNN_eqb_eq in HZ. subst zs.
  apply listNN_eqb_eq in HU. subst us.
  inversion H; clear H; subst.
  cbn [eff_ret]. unfold brk_resolution_ok, brk_model.
  repeat split; try reflexivity. exact HR.
Qed.

Lemma check_brk_ok_intro : forall req r m,
  brk_resolution_ok m req r ->
  check_brk req (mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps m)))
                              (brk_unmaps r (vm_brk (m_vmmaps m))) [] []) m
  = CheckOk (brk_model req r m) [].
Proof.
  intros req r m HR. unfold brk_resolution_ok in HR.
  unfold check_brk. rewrite HR.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
  unfold brk_model. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_ok_iff : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 214%Z ->
  (syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) <->
   (eff = mkEffectU (eff_ret eff) []
            (brk_zeros (ms_gpr ms 0) (eff_ret eff) (vm_brk (m_vmmaps model)))
            (brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps model))) [] []
    /\ evs = []
    /\ brk_resolution_ok model (ms_gpr ms 0) (eff_ret eff)
    /\ model' = brk_model (ms_gpr ms 0) (eff_ret eff) model)).
Proof.
  intros segs ms x8 model eff model' evs Hno. split.
  - intro H. apply (proj1 (syscall_spec_brk _ _ _ _ _ Hno)) in H.
    apply check_brk_complete_ok in H.
    apply check_brk_ok_inv in H. exact H.
  - intros (Heff & -> & Hok & ->).
    apply (proj2 (syscall_spec_brk _ _ _ _ _ Hno)). apply check_brk_sound_ok.
    rewrite Heff at 1. cbn [eff_ret].
    apply check_brk_ok_intro. exact Hok.
Qed.

Lemma brk_ok_intro : forall segs ms x8 model r,
  bv_unsigned x8 = 214%Z ->
  brk_resolution_ok model (ms_gpr ms 0) r ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                        (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])
        (brk_model (ms_gpr ms 0) r model) []).
Proof.
  intros segs ms x8 model r Hno Hok.
  apply (brk_ok_iff segs ms x8 model _ _ _ Hno). cbn [eff_ret]. auto.
Qed.

(* [comment removed for export] *)
Lemma brk_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 214%Z ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno H.
  apply (proj1 (syscall_spec_brk _ _ _ _ _ Hno)) in H.
  apply (check_brk_complete_unmodeled _ _ _ (mkEffect (Z_to_bv 64 0) [] [])) in H.
  unfold check_brk in H.
  destruct (Mmap.brk_r_ok model (ms_gpr ms 0) (Z_to_bv 64 0)
            && listNN_eqb []
                 (brk_zeros (ms_gpr ms 0) (Z_to_bv 64 0) (vm_brk (m_vmmaps model)))
            && listNN_eqb []
                 (brk_unmaps (Z_to_bv 64 0) (vm_brk (m_vmmaps model))));
    discriminate.
Qed.

(* [comment removed for export] *)
Lemma brk_receptive : forall segs ms x8 model,
  bv_unsigned x8 = 214%Z ->
  exists eff model',
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []).
Proof.
  intros segs ms x8 model Hno.
  pose (r := vm_brk (m_vmmaps model)).
  exists (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                        (brk_unmaps r (vm_brk (m_vmmaps model))) [] []),
         (brk_model (ms_gpr ms 0) r model).
  apply brk_ok_intro; [exact Hno|].
  unfold brk_resolution_ok, Mmap.brk_r_ok, r. cbv zeta.
  destruct (w_is0 (ms_gpr ms 0)
            || Z.ltb (bv_unsigned (ms_gpr ms 0))
                     (bv_unsigned (min_brk (m_vmmaps model)))).
  - apply bv_eqb_refl.
  - destruct (Z.ltb (bv_unsigned (ms_gpr ms 0))
                    (bv_unsigned (vm_brk (m_vmmaps model)))).
    + rewrite bv_eqb_refl, orb_true_r. reflexivity.
    + rewrite bv_eqb_refl, orb_true_r, andb_true_l.
      unfold brk_grow_ok, Mmap.brk_grow_ok.
      now rewrite Z.ltb_irrefl, andb_false_r.
Qed.

(* [comment removed for export] *)
Lemma brk_zeros_grow : forall req r old,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
  brk_zeros req r old =
    brk_page_range (page_round_up_Z (bv_unsigned old))
                   (page_round_up_Z (bv_unsigned r)).
Proof.
  intros req r old Hreq Hold Hlt. unfold brk_zeros, brk_is_grow.
  assert (E1 : w_is0 req = false)
    by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
  assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2, E3. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_grants_grow : forall req r old,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
  brk_grants req r old =
    brk_page_range (page_round_up_Z (bv_unsigned old))
                   (page_round_up_Z (bv_unsigned r)).
Proof.
  intros req r old Hreq Hold Hlt. unfold brk_grants, brk_is_grow.
  assert (E1 : w_is0 req = false)
    by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
  assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2, E3. reflexivity.
Qed.

Lemma brk_grants_is_brk_zeros : forall req r old,
  brk_grants req r old = brk_zeros req r old.
Proof. reflexivity. Qed.

Lemma brk_zeros_query : forall r old, brk_zeros (Z_to_bv 64 0) r old = [].
Proof.
  intros r old. unfold brk_zeros, brk_is_grow, w_is0.
  rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma brk_grants_query : forall r old, brk_grants (Z_to_bv 64 0) r old = [].
Proof.
  intros r old. unfold brk_grants, brk_is_grow, w_is0.
  rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma brk_zeros_keep : forall req old, brk_zeros req old old = [].
Proof.
  intros req old. unfold brk_zeros, brk_is_grow.
  rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.

Lemma brk_grants_keep : forall req old, brk_grants req old old = [].
Proof.
  intros req old. unfold brk_grants, brk_is_grow.
  rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_unmaps_keep : forall old, brk_unmaps old old = [].
Proof.
  intros old. unfold brk_unmaps. cbv zeta.
  destruct (0 <? bv_unsigned old)%Z eqn:E; [|reflexivity].
  unfold brk_page_range. rewrite Z.ltb_irrefl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_unmaps_query : forall h r,
  r = vm_brk h -> brk_unmaps r (vm_brk h) = [].
Proof. intros h r ->. apply brk_unmaps_keep. Qed.

(* [comment removed for export] *)
Lemma brk_unmaps_grow : forall r old,
  (bv_unsigned old <= bv_unsigned r)%Z -> brk_unmaps r old = [].
Proof.
  intros r old H. unfold brk_unmaps. cbv zeta.
  destruct (0 <? bv_unsigned old)%Z eqn:E0; [|reflexivity].
  assert (E : (page_round_up_Z (bv_unsigned r)
               <? page_round_up_Z (bv_unsigned old))%Z = false)
    by (apply Z.ltb_ge, page_round_up_Z_mono, H).
  unfold brk_page_range. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_grow : forall h req r,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned (vm_brk h))%Z -> (bv_unsigned (vm_brk h) < bv_unsigned r)%Z ->
  brk_grow_ok h req r
  = ((if (page_round_up_Z (bv_unsigned (vm_brk h))
          <? page_round_up_Z (bv_unsigned r))%Z
      then (page_round_up_Z (bv_unsigned r) <=? alloc_top h)%Z
           && region_free (vm_reserved h ++ vm_maps h)
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (vm_brk h))))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size
                             - page_round_up_Z (bv_unsigned (vm_brk h))))
      else true)
     && (vm_backed_bytes h + brk_grow_bytes h r <=? vm_limit h)%Z)%bool.
Proof.
  intros h req r Hreq H0 Hlt.
  assert (Hmaps : m_vmmaps (vm_model h) = h) by reflexivity.
  assert (Hbacked : vm_backing_used (vm_model h) = vm_backed_bytes h).
  { unfold vm_backing_used, vm_model.
    cbv [mkModel m_vmmaps m_vm m_vm_lazy m_vm_materialized
         vmst_lazy vmst_materialized].
    change ((live_bytes (vm_backed_maps h) + 0)%Z =
            live_bytes (vm_backed_maps h)).
    apply Z.add_0_r. }
  unfold brk_grow_ok, Mmap.brk_grow_ok, Mmap.brk_budget_ok.
  rewrite Hmaps, Hbacked.
  assert (E2 : (0 <? bv_unsigned (vm_brk h))%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned (vm_brk h) <? bv_unsigned r)%Z = true)
    by (apply Z.ltb_lt; lia).
  rewrite E2, E3. reflexivity.
Qed.

Lemma brk_grow_ok_keep : forall h req,
  brk_grow_ok h req (vm_brk h) = true.
Proof.
  intros h req. unfold brk_grow_ok, Mmap.brk_grow_ok.
  cbv [vm_model mkModel m_vmmaps m_vm vm_backing_used m_vm_lazy
       m_vm_materialized vmst_lazy vmst_materialized].
  cbn [vmst_maps vm_backed_bytes maps_subtract_all].
  rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_aligned : forall z,
  (0 <= z)%Z -> (z mod page_size = 0)%Z -> page_round_up_Z z = z.
Proof.
  intros z Hz Hmod. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod z 4096 ltac:(lia)) as Hdiv.
  replace (z + 4096 - 1)%Z with
    (4095 + (z / 4096) * 4096)%Z by lia.
  rewrite Z.div_add by lia.
  rewrite Z.div_small by lia. lia.
Qed.

Lemma page_round_up_Z_bounds : forall z,
  (0 <= z)%Z ->
  (z <= page_round_up_Z z <= z + page_size - 1)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hmod.
  lia.
Qed.

(* [comment removed for export] *)
Lemma round8_le_page_round : forall z,
  (0 <= z)%Z ->
  ((((z + 7) / 8) * 8) <= page_round_up_Z z)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z.
  pose proof (Z.div_mod (z + 7) 8 ltac:(lia)) as H8.
  pose proof (Z.mod_pos_bound (z + 7) 8 ltac:(lia)) as H8mod.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hp.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hpmod.
  assert (H8ceil :
    (z <= ((z + 7) / 8) * 8 <= z + 7)%Z) by lia.
  assert (Hpceil :
    (z <= ((z + 4096 - 1) / 4096) * 4096)%Z) by lia.
  set (q8 := ((z + 7) / 8)%Z) in *.
  set (qp := ((z + 4096 - 1) / 4096)%Z) in *.
  assert (Hq : (q8 <= 512 * qp)%Z) by lia.
  change (q8 * 8 <= qp * 4096)%Z.
  lia.
Qed.

Lemma round8_le_page_grant : forall old n,
  (0 <= old)%Z -> (0 <= n)%Z ->
  (old mod page_size = 0)%Z ->
  ((((n + 7) / 8) * 8) <= page_round_up_Z (old + n) - old)%Z.
Proof.
  intros old n Hold Hn Hmod.
  unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod old 4096 ltac:(lia)) as Holddiv.
  replace (old + n + 4096 - 1)%Z with
    ((n + 4096 - 1) + (old / 4096) * 4096)%Z by lia.
  rewrite Z.div_add by lia.
  pose proof (round8_le_page_round n Hn).
  unfold page_round_up_Z in *. lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_prefix : forall maps b small big,
  (bv_unsigned small <= bv_unsigned big)%Z ->
  region_free maps b big = true -> region_free maps b small = true.
Proof.
  induction maps as [|[a sz] maps IH]; intros b small big Hle Hfree;
    [reflexivity|].
  cbn [region_free] in Hfree |- *.
  apply andb_true_iff in Hfree as [Hhead Htail].
  apply andb_true_iff. split; [|eapply IH; eassumption].
  apply negb_true_iff in Hhead. apply negb_true_iff.
  unfold iv_overlap in Hhead |- *.
  apply andb_false_iff in Hhead. apply andb_false_iff.
  destruct Hhead as [Hhead|Hhead]; [left|right];
    apply Z.ltb_ge in Hhead; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_grow : forall h req r,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) < bv_unsigned r)%Z ->
  (bv_unsigned (vm_brk h) mod page_size = 0)%Z ->
  brk_grow_ok h req r
  = (((page_round_up_Z (bv_unsigned r) <=? alloc_top h)%Z
      && region_free (vm_reserved h ++ vm_maps h) (vm_brk h)
           (Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size
                        - bv_unsigned (vm_brk h))))
     && (vm_backed_bytes h + brk_grow_bytes h r <=? vm_limit h)%Z)%bool.
Proof.
  intros h req r Hreq Hpos Hlt Halign.
  rewrite brk_grow_ok_grow by assumption.
  rewrite (page_round_up_Z_aligned (bv_unsigned (vm_brk h))) by lia.
  assert (Hround : (bv_unsigned (vm_brk h)
                    < page_round_up_Z (bv_unsigned r))%Z).
  { pose proof (page_round_up_Z_bounds (bv_unsigned r) ltac:(lia)). lia. }
  rewrite (proj2 (Z.ltb_lt _ _) Hround).
  replace (Z_to_bv 64 (bv_unsigned (vm_brk h))) with (vm_brk h).
  - reflexivity.
  - symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma brk_zeros_aligned_grow : forall req r old,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
  (bv_unsigned old mod page_size = 0)%Z ->
  brk_zeros req r old =
    [(old, Z_to_bv 64 (page_round_up_Z (bv_unsigned r) - bv_unsigned old))].
Proof.
  intros req r old Hreq Hpos Hlt Halign.
  rewrite brk_zeros_grow by assumption.
  rewrite (page_round_up_Z_aligned (bv_unsigned old)) by lia.
  unfold brk_page_range.
  assert (Hround : (bv_unsigned old < page_round_up_Z (bv_unsigned r))%Z).
  { pose proof (page_round_up_Z_bounds (bv_unsigned r) ltac:(lia)). lia. }
  rewrite (proj2 (Z.ltb_lt _ _) Hround).
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_aligned_grant_ok :
  forall (res : list (word * word)) (r w g : word) (top ceil : Z),
  bv_unsigned (r + w) = (bv_unsigned r + bv_unsigned w)%Z ->
  bv_unsigned (r + w) = top ->
  g = Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r) ->
  (ceil + page_size < 2 ^ 64)%Z ->
  (page_round_up_Z (bv_unsigned (r + w)) <= ceil)%Z ->
  region_free res r
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
                 - bv_unsigned r)) = true ->
     bv_unsigned g = (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r)%Z
  /\ (bv_unsigned w <= bv_unsigned g)%Z
  /\ (bv_unsigned r + bv_unsigned g <= ceil)%Z
  /\ (top <= ceil)%Z
  /\ region_free res r w = true
  /\ region_free res r g = true.
Proof.
  intros res r w g top ceil Hnowrap Htop Hg Hacp Hceil Hfree.
  pose proof (u64_range r). pose proof (u64_range w).
  pose proof (page_round_up_Z_bounds (bv_unsigned (r + w))
                (proj1 (u64_range (r + w)))).
  assert (Hps : (0 < page_size)%Z) by (vm_compute; reflexivity).
  (* [StepTac.u_Z2bv] is downstream of this file, so reprove it here. *)
  assert (Hu : forall z, (0 <= z)%Z -> (z < 2 ^ 64)%Z ->
                 bv_unsigned (Z_to_bv 64 z) = z).
  { intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. apply Z.mod_small.
    split; [exact Hlo | exact Hhi]. }
  assert (HgU : bv_unsigned g
                = (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r)%Z)
    by (subst g; apply Hu; lia).
  repeat split; rewrite ?HgU; try lia.
  (* the gate tests one page more than the grant, so both the request and
     the grant are prefixes of the range [Hfree] covers *)
  - apply (region_free_prefix res r w
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
                          - bv_unsigned r)));
      [rewrite Hu by lia; lia | exact Hfree].
  - apply (region_free_prefix res r g
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
                          - bv_unsigned r)));
      [rewrite HgU, Hu by lia; lia | exact Hfree].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition growable (reserved : list (word * word)) (lim top : Z) (t r : word)
    : Prop :=
  r <> Z_to_bv 64 0 /\ (bv_unsigned r + bv_unsigned t < 2 ^ 64)%Z /\
  (t = Z_to_bv 64 0 \/
   (((if (page_round_up_Z (bv_unsigned r)
          <? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
      then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
            <=? top)%Z
           && region_free reserved
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
                (Z_to_bv 64 (page_round_up_Z
                               (bv_unsigned r + bv_unsigned t)
                              + page_size - page_round_up_Z (bv_unsigned r)))
      else true)
     && (Z.max 0 (page_round_up_Z (bv_unsigned r + bv_unsigned t)
                  - page_round_up_Z (bv_unsigned r)) <=? lim)%Z)%bool = true)).

(* [comment removed for export] *)
Definition T1 (reserved : list (word * word)) (lim top : Z) (t : word)
    (bufs : list (list byte))
    (r : word) : (list (list byte) * word) -> Prop :=
  fun o => (o = ([], Z_to_bv 64 4)
            /\ (r = Z_to_bv 64 0
                \/ (2 ^ 64 <= bv_unsigned r + bv_unsigned t)%Z
                \/ t <> Z_to_bv 64 0))
        \/ (growable reserved lim top t r /\ o = (bufs, Z_to_bv 64 0)).

(* [comment removed for export] *)
Definition T2 (want : word) (bufs : list (list byte)) (r2 : word)
    : (list (list byte) * word) -> Prop :=
  fun o => (r2 = want /\ o = (bufs, Z_to_bv 64 0))
        \/ (r2 <> want /\ o = ([], Z_to_bv 64 4)).

(* [comment removed for export] *)
Lemma brk_r_ok_query_iff : forall h r,
  brk_r_ok h (Z_to_bv 64 0) r <-> r = vm_brk h.
Proof.
  intros h r. unfold brk_r_ok, Mmap.brk_r_ok.
  cbv [vm_model mkModel m_vmmaps m_vm]. cbv zeta.
  unfold w_is0. rewrite bv_eqb_refl. cbn [orb].
  apply bv_eqb_eq.
Qed.

(* [comment removed for export] *)
Lemma reserved_top_above : forall reserved (r : Z),
  (reserved_top reserved <= r)%Z ->
  Forall (fun p : word * word =>
            (bv_unsigned (fst p) + bv_unsigned (snd p) <= r)%Z) reserved.
Proof.
  induction reserved as [|[a sz] l IH]; intros r Hr; cbn [reserved_top] in *.
  - constructor.
  - constructor; [cbn [fst snd]; lia | apply IH; lia].
Qed.

(* [comment removed for export] *)
Lemma region_free_above_top : forall reserved (lo n : word),
  (reserved_top reserved <= bv_unsigned lo)%Z ->
  region_free reserved lo n = true.
Proof.
  induction reserved as [|[a sz] l IH]; intros lo n Hr;
    cbn [reserved_top] in *; [reflexivity|].
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E. cbn [andb negb]. apply IH. lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_above : forall (l : list (word * word)) (lo n : word),
  Forall (fun p => (bv_unsigned (fst p) + bv_unsigned (snd p)
                    <= bv_unsigned lo)%Z) l ->
  region_free l lo n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
  inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E. cbn [andb negb]. apply IH. exact Hl.
Qed.

(* [comment removed for export] *)
Lemma region_free_below : forall (l : list (word * word)) (lo n : word),
  Forall (fun p => (bv_unsigned lo + bv_unsigned n
                    <= bv_unsigned (fst p))%Z) l ->
  region_free l lo n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
  inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned a <? bv_unsigned lo + bv_unsigned n)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E, andb_false_r. cbn [negb andb]. apply IH. exact Hl.
Qed.

(* [comment removed for export] *)
Lemma growable_aligned_grow : forall reserved lim top (t r : word),
  (bv_unsigned r mod page_size = 0)%Z ->
  (reserved_top reserved <= bv_unsigned r)%Z ->
  (0 < bv_unsigned t)%Z ->
  (bv_unsigned r + bv_unsigned t + page_size - 1 <= top)%Z ->
  (bv_unsigned t <= lim)%Z ->
  ((if (page_round_up_Z (bv_unsigned r)
        <? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
    then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
          <=? top)%Z
         && region_free reserved
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
              (Z_to_bv 64 (page_round_up_Z
                             (bv_unsigned r + bv_unsigned t)
                            + page_size - page_round_up_Z (bv_unsigned r)))
    else true)
   && (bv_unsigned t <=? lim)%Z)%bool = true.
Proof.
  intros reserved lim top t r Halign Htop Hpos Hceil Hlim.
  pose proof (proj1 (u64_range r)) as Hr0.
  rewrite (page_round_up_Z_aligned (bv_unsigned r)); [|lia|exact Halign].
  assert (Hru := page_round_up_Z_bounds
    (bv_unsigned r + bv_unsigned t) ltac:(lia)).
  assert (Hltpage :
    (bv_unsigned r < page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z)
    by lia.
  rewrite (proj2 (Z.ltb_lt _ _) Hltpage).
  apply andb_true_iff. split; [apply andb_true_iff; split|].
  - apply Z.leb_le. lia.
  - rewrite Z_to_bv_bv_unsigned. apply region_free_above_top. exact Htop.
  - apply Z.leb_le. exact Hlim.
Qed.

Lemma growable_aligned_grow_rounded : forall reserved lim top (t r : word),
  (bv_unsigned r mod page_size = 0)%Z ->
  (reserved_top reserved <= bv_unsigned r)%Z ->
  (0 < bv_unsigned t)%Z ->
  (bv_unsigned r + bv_unsigned t + page_size - 1 <= top)%Z ->
  (Z.max 0 (page_round_up_Z (bv_unsigned r + bv_unsigned t)
            - page_round_up_Z (bv_unsigned r)) <= lim)%Z ->
  ((if (page_round_up_Z (bv_unsigned r)
        <? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
    then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
          <=? top)%Z
         && region_free reserved
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
              (Z_to_bv 64 (page_round_up_Z
                             (bv_unsigned r + bv_unsigned t)
                            + page_size - page_round_up_Z (bv_unsigned r)))
    else true)
   && (Z.max 0 (page_round_up_Z (bv_unsigned r + bv_unsigned t)
                - page_round_up_Z (bv_unsigned r)) <=? lim)%Z)%bool = true.
Proof.
  intros reserved lim top t r Halign Htop Hpos Hceil Hlim.
  apply andb_true_iff. split.
  - pose proof (growable_aligned_grow reserved
                  (bv_unsigned t) top t r Halign Htop Hpos Hceil
                  (Z.le_refl _)) as Hg.
    apply andb_true_iff in Hg as [Hg _]. exact Hg.
  - apply Z.leb_le. exact Hlim.
Qed.

Lemma brk_aslr_max_val : brk_aslr_max = 1073741824%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma brk_model_next_query : forall h r,
  r = vm_brk h ->
  brk_model_next h (Z_to_bv 64 0) r
  = mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h)
      (vm_start_brk h) r (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros h r ->. unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r.
  rewrite brk_grants_query, brk_unmaps_keep. reflexivity.
Qed.

Lemma brk_model_query : forall r m,
  r = vm_brk (m_vmmaps m) ->
  brk_model (Z_to_bv 64 0) r m
  = with_vmmaps
      (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
        (vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m)) r
        (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
        (vm_init_sp (m_vmmaps m))) m.
Proof.
  intros r m ->. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  rewrite brk_model_next_query by reflexivity. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_r_ok_grow_iff : forall reserved lim s r maps noaccess mb sp req r2,
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned s <= bv_unsigned req)%Z ->
  (bv_unsigned r <= bv_unsigned req)%Z ->
  (brk_r_ok (mkVmMapsFull reserved maps noaccess s r lim mb sp) req r2 <->
   (r2 = req \/ r2 = r)
   /\ brk_grow_ok (mkVmMapsFull reserved maps noaccess s r lim mb sp) req r2 = true).
Proof.
  intros reserved lim s r maps noaccess mb sp req r2 Hpos Hs Hreq.
  unfold brk_r_ok, Mmap.brk_r_ok.
  cbv [vm_model mkModel m_vmmaps m_vm]. cbv zeta.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    apply Z.eqb_neq. lia. }
  rewrite E0.
  assert (Hmin : (bv_unsigned req <?
                   bv_unsigned (min_brk (mkVmMapsFull reserved maps noaccess s r lim mb sp)))%Z
                 = false).
  { apply Z.ltb_ge. unfold min_brk. cbn [vm_start_brk]. lia. }
  cbn [vmst_maps]. rewrite Hmin. cbn [orb vm_brk].
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned r)) ltac:(lia)).
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. tauto.
Qed.

(* [comment removed for export] *)
Lemma T1_iff_T2 : forall reserved lim s (mb sp : word) t bufs r,
  r <> Z_to_bv 64 0 -> (bv_unsigned s <= bv_unsigned r)%Z ->
  (bv_unsigned r + bv_unsigned t < 2 ^ 64)%Z ->
  forall o, T1 reserved lim (bv_unsigned sp - stack_max_size) t bufs r o <->
    (exists r2, brk_r_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2
                /\ T2 (r + t) bufs r2 o).
Proof.
  intros reserved lim s mb sp t bufs r Hr0 Hs Hnw o.
  pose proof (u64_range r) as Hur. pose proof (u64_range t) as Hut.
  pose proof (word_neq0_unsigned r Hr0) as Hur0.
  assert (Huadd : bv_unsigned (r + t) = (bv_unsigned r + bv_unsigned t)%Z)
    by (apply u_add_small; exact Hnw).
  assert (Hwant0 : r + t <> Z_to_bv 64 0).
  { intro He. apply (f_equal bv_unsigned) in He.
    rewrite Huadd in He.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia. }
  assert (Bridge : forall r2,
             brk_r_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 <->
             (r2 = r + t \/ r2 = r)
             /\ brk_grow_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2
                = true)
    by (intro r2; apply brk_r_ok_grow_iff with (maps := []) (noaccess := []); lia).
  split.
  - intros [[-> Hcase] | [Hg ->]].
    + (* exit 4: failure resolution r2 = r, which exists iff t <> 0 *)
      assert (Ht0 : t <> Z_to_bv 64 0)
        by (destruct Hcase as [Hc | [Hc | Hc]]; [congruence | lia | exact Hc]).
      pose proof (word_neq0_unsigned t Ht0) as Hut0.
      exists r. split.
      * apply Bridge. split; [right; reflexivity|].
        exact (brk_grow_ok_keep (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t)).
      * right. split; [| reflexivity].
        intro He. apply (f_equal bv_unsigned) in He.
        rewrite Huadd in He. lia.
    + (* success: r2 = want *)
      destruct Hg as (_ & _ & Hb).
      exists (r + t). split.
      * apply Bridge. split; [left; reflexivity|].
        destruct (Z.eq_dec (bv_unsigned t) 0) as [Hz | Hz].
        { assert (Ht0 : t = Z_to_bv 64 0)
            by (apply bv_eq; rewrite Hz; reflexivity).
          rewrite Ht0, word_add_0_r.
          exact (brk_grow_ok_keep (mkVmMapsFull reserved [] [] s r lim mb sp) r). }
        destruct Hb as [Hb | Hb];
          [exfalso; apply Hz; rewrite Hb; reflexivity |].
        rewrite brk_grow_ok_grow;
          cbn [vm_brk vm_reserved vm_maps vm_limit vm_live_bytes live_bytes];
          [| exact Hwant0 | lia | lia].
        unfold brk_grow_bytes. cbn [vm_brk].
        rewrite app_nil_r, Huadd, Z.add_0_l.
        exact Hb.
      * left. split; reflexivity.
  - intros (r2 & Hrok & Hb).
    apply Bridge in Hrok. destruct Hrok as (Hcase & Hgrow).
    destruct Hb as [[-> ->] | [Hne ->]].
    + (* success resolution *)
      right. split; [| reflexivity].
      split; [exact Hr0 | split; [exact Hnw |]].
      destruct (Z.eq_dec (bv_unsigned t) 0) as [Hz | Hz];
        [left; apply bv_eq; rewrite Hz; reflexivity | right].
      rewrite brk_grow_ok_grow in Hgrow;
        cbn [vm_brk vm_reserved vm_maps vm_limit vm_live_bytes live_bytes] in *;
        [| exact Hwant0 | lia | lia].
      unfold brk_grow_bytes in Hgrow. cbn [vm_brk] in Hgrow.
      rewrite app_nil_r, Huadd, Z.add_0_l in Hgrow.
      exact Hgrow.
    + (* failure resolution: r2 = r, and t <> 0 or r2 = want *)
      left. split; [reflexivity |].
      right. right.
      intro Ht0. subst t.
      rewrite word_add_0_r in Hne, Hcase.
      destruct Hcase as [Hc | Hc]; exact (Hne Hc).
Qed.

Lemma T2_fail_iff : forall want bufs r2,
  r2 <> want -> forall o, T2 want bufs r2 o <-> o = ([], Z_to_bv 64 4).
Proof.
  intros want bufs r2 Hne o. unfold T2. tauto.
Qed.

Lemma T2_succ_iff : forall want bufs o,
  T2 want bufs want o <-> o = (bufs, Z_to_bv 64 0).
Proof.
  intros want bufs o. unfold T2. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Inductive to_outcomes : machine_state -> Model -> ((list (list byte) * word) -> Prop) -> Prop :=
| tou_wexit : forall ms model bufs code (U : (list (list byte) * word) -> Prop),
    fd1chan model ->
    to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
    bufs_modeled bufs ->
    (forall o, U o <-> o = (bufs, code)) ->
    to_outcomes ms model U
| tou_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_outcomes ms' model U ->
    to_outcomes ms model U
| tou_brk : forall ms model x8
    (T : SyscallEffect -> Model -> (list (list byte) * word) -> Prop)
    (U : (list (list byte) * word) -> Prop),
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 214%Z ->
    (forall eff model' evs,
       syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
       to_outcomes (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_outcomes ms model U.

(* [comment removed for export] *)
Lemma tou_msteps : forall ms ms' model U,
  msteps segs ms ms' -> to_outcomes ms' model U -> to_outcomes ms model U.
Proof.
  intros ms ms' model U H; induction H; [auto|].
  intro Ht. eapply tou_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma forget_vm_ranges_frame : forall ranges model,
  m_halted (forget_vm_ranges ranges model) = m_halted model /\
  m_fs (forget_vm_ranges ranges model) = m_fs model /\
  m_fds (forget_vm_ranges ranges model) = m_fds model /\
  (m_vm_lazy model = [] -> m_vm_lazy (forget_vm_ranges ranges model) = []).
Proof.
  induction ranges as [|[a n] ranges IH]; intros model; cbn [forget_vm_ranges].
  - auto.
  - specialize (IH (vm_forget_range (bv_unsigned a)
      (bv_unsigned a + bv_unsigned n) model)).
    destruct IH as (Hhalt & Hfs & Hfds & Hlazy).
    unfold vm_forget_range, with_vm_backing in Hhalt, Hfs, Hfds, Hlazy.
    cbn [m_halted m_fs m_fds m_vm_lazy] in Hhalt, Hfs, Hfds, Hlazy.
    repeat split; try assumption.
    intro Hempty. apply Hlazy. rewrite Hempty. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_step_shape : forall ms x8 model eff model' evs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  bv_unsigned x8 = 214%Z ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\ m_halted model' = None /\ m_fs model' = m_fs model
  /\ m_fds model' = m_fds model
  /\ m_vm_lazy model' = m_vm_lazy model.
Proof.
  intros ms x8 model eff model' evs Hh Hlazy Hno Hs.
  apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hs.
  destruct Hs as (_ & -> & _ & ->).
  unfold brk_model, with_brk_next. cbv zeta.
  destruct (forget_vm_ranges_frame
    (brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps model)))
    (with_vmmaps
      (brk_model_next (m_vmmaps model) (ms_gpr ms 0) (eff_ret eff)) model))
    as (Hhalt & Hfs & Hfds & Hlazy').
  repeat split.
  - rewrite Hhalt. unfold with_vmmaps. cbn [m_halted]. exact Hh.
  - rewrite Hfs. unfold with_vmmaps. reflexivity.
  - rewrite Hfds. unfold with_vmmaps. reflexivity.
  - rewrite Hlazy. apply Hlazy'.
    unfold with_vmmaps. cbn [m_vm_lazy]. exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma sstep_brk_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 214%Z ->
  sstep segs (mkCfg ms model) evs st ->
  exists eff model',
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []) /\
    evs = [] /\
    st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model').
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    assert (Hx : x0 = x8) by congruence; subst x0.
    destruct (brk_step_shape ms x8 model eff model' evs Hh Hlazy Hno H3)
      as (He & _ & _ & _ & Hlazy').
    subst evs.
    rewrite (materialize_model_accesses_no_lazy _ _
      (eq_trans Hlazy' Hlazy)) in H7.
    inversion H7; subst model''.
    exists eff, model'; auto.
  - (* sstep_syscall_materialization_fault: no lazy range can fault *)
    exfalso.
    match goal with
    | Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec)
        as (He & _ & _ & _ & Hlazy'); subst evs0;
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)) in Hmat;
      discriminate
    end.
  - (* sstep_exit: brk cannot halt the model *)
    exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hhalt : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
      congruence
    end.
  - (* sstep_killed: brk cannot kill it either *)
    exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hkill : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
      assert (Hhn : m_halted model' = None) by congruence;
      rewrite (m_killed_of_m_halted_none _ Hhn) in Hkill; discriminate
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (brk_no_unmodeled segs ms x8 model Hno Hspec)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition outcome_trace (fs : Fs.Fs) (o : list (list byte) * word) : list event :=
  wevents (fst o) ++ [ExitEv (snd o) fs].

(* [comment removed for export] *)
Definition outcomes_post (fs : Fs.Fs) (U : (list (list byte) * word) -> Prop) : post :=
  fun tr o => exists out, U out /\ tr = outcome_trace fs out /\ exits_with (snd out) tr o.

Lemma to_outcomes_exec : forall ms model U,
  to_outcomes ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  OmniRun.exec segs (mkCfg ms model) (outcomes_post (m_fs model) U).
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy.
  - (* tou_wexit *)
    eapply exec_conseq;
      [exact (to_wallexit_exec segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 bufs code ms model
                Hh Hlazy (fd1chan_fdchan model Hfd) Hbm Hte) |].
    intros tr o (Heq & Hx). exists (bufs, code).
    split; [apply HU; reflexivity |].
    split; [unfold outcome_trace; cbn [fst snd]; rewrite <- wevents_ch_fd1; exact Heq |].
    cbn [snd]. exact Hx.
  - (* tou_step *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hh Hlazy) |]. intros tr o H. cbn [app]. exact H.
  - (* tou_brk: every admissible resolution is a successor *)
    apply exec_step; [exact Hh | | |].
    + destruct (brk_receptive segs ms x8 model Hno) as (eff & model' & Hspec).
      destruct (brk_step_shape ms x8 model eff model' [] Hh Hlazy Hno Hspec)
        as (_ & Hh' & _ & _ & Hlazy').
      eexists; eexists.
      apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)). reflexivity.
    + intros evs Hss.
      destruct (sstep_brk_inv ms model x8 evs SError Hh Hlazy Hsvc Hno Hss)
        as (eff & model' & _ & _ & Habs). discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_brk_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hss)
        as (eff & model' & Hspec & -> & Hc'). injection Hc' as ->.
      destruct (brk_step_shape ms x8 model eff model' [] Hh Hlazy Hno Hspec)
        as (_ & Hh' & Hfs & _ & Hlazy').
      eapply exec_conseq; [exact (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy)) |].
      intros tr o (out & Hout & Heq & Hx). exists out.
      split; [apply HU; exists eff, model', []; split; [exact Hspec | exact Hout] |].
      split; [| exact Hx].
      cbn [app]. unfold outcome_trace in Heq |- *. rewrite Hfs in Heq. exact Heq.
Qed.

(* [comment removed for export] *)
Lemma to_outcomes_no_other_exit : forall ms model U,
  to_outcomes ms model U -> m_halted model = None -> m_vm_lazy model = [] ->
  forall code', (forall o, U o -> snd o <> code') ->
  ~ OmniRun.exec segs (mkCfg ms model) (exits_with code').
Proof.
  intros ms model U Hto Hh Hlazy code' Hne Hex.
  destruct (exec_realizes _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy))
    as (tr & [c' | c'] & Hm & (out & Hout & _ & Hx)); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'.
  exact (Hne out Hout Hx').
Qed.

Lemma to_outcomes_not_silent : forall ms model U,
  to_outcomes ms model U -> m_halted model = None -> m_vm_lazy model = [] ->
  ~ cosafe segs (mkCfg ms model) (fun tr => tr = []).
Proof.
  intros ms model U Hto Hh Hlazy Hc.
  destruct (exec_realizes _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy))
    as (tr & [c' | c'] & Hm & (out & _ & Heq & Hx)); [| destruct Hx].
  destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
  subst tr. unfold outcome_trace in Hnil.
  destruct (wevents (fst out)); discriminate Hnil.
Qed.

Lemma to_outcomes_star_only : forall ms model U,
  to_outcomes ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    exists o, U o /\ is_prefix tr (outcome_trace (m_fs model) o).
Proof.
  intros ms model U Hto Hh Hlazy tr c Hstar.
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy) Hstar))
    as (tr' & o & _ & (out & Hout & Heq & _)).
  exists out. split; [exact Hout |]. rewrite <- Heq. apply is_prefix_app.
Qed.

Lemma to_outcomes_star_admits : forall ms model U,
  to_outcomes ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall o, U o ->
    exists c, star segs (mkCfg ms model) (outcome_trace (m_fs model) o) c.
Proof.
  intros ms model U Hto.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy o Ho.
  - (* tou_wexit *)
    apply HU in Ho. subst o.
    unfold outcome_trace; cbn [fst snd].
    rewrite <- wevents_ch_fd1.
    eapply (to_wallexit_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1);
      [exact Hh | exact Hlazy | exact (fd1chan_fdchan model Hfd)
      | exact Hbm | exact Hte].
  - (* tou_step *)
    destruct (IH Hh Hlazy o Ho) as [c Hstar].
    exists c.
    replace (outcome_trace (m_fs model) o)
      with ([] ++ outcome_trace (m_fs model) o) by reflexivity.
    eapply star_step; [|exact Hstar].
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - (* tou_brk *)
    apply HU in Ho.
    destruct Ho as (eff & model' & evs & Hspec & Ht).
    destruct (brk_step_shape ms x8 model eff model' evs Hh Hlazy Hno Hspec)
      as (Hevs & Hh' & Hfs & _ & Hlazy'). subst evs.
    destruct (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy) o Ht)
      as [c Hstar].
    exists c.
    replace (outcome_trace (m_fs model) o)
      with ([] ++ outcome_trace (m_fs model') o)
      by (unfold outcome_trace; rewrite Hfs; reflexivity).
    eapply star_step; [|exact Hstar].
    apply (sstep_syscall segs ms model x8 eff model' model' []);
      try assumption.
    rewrite (materialize_model_accesses_no_lazy _ _
      (eq_trans Hlazy' Hlazy)).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_outcomes_no_error : forall ms model U,
  to_outcomes ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model U Hto Hh Hlazy. apply exec_no_error.
  eapply exec_conseq; [exact (to_outcomes_exec ms model U Hto Hh Hlazy) |].
  intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tou_brk_r : forall ms model x8 (T' : word -> (list (list byte) * word) -> Prop) U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 214%Z ->
  (forall r,
     brk_resolution_ok model (ms_gpr ms 0) r ->
     to_outcomes
       (advance_past_svc (apply_effect ms
          (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                          (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])))
       (brk_model (ms_gpr ms 0) r model)
       (T' r)) ->
  (forall o, U o <->
     (exists r, brk_resolution_ok model (ms_gpr ms 0) r /\ T' r o)) ->
  to_outcomes ms model U.
Proof.
  intros ms model x8 T' U Hsvc Hno Hcont HU.
  apply (tou_brk ms model x8 (fun eff _ => T' (eff_ret eff)) U);
    [exact Hsvc | exact Hno | |].
  - intros eff model' evs Hspec.
    apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hspec.
    destruct Hspec as (Heff & _ & Hok & ->).
    pose proof (Hcont (eff_ret eff) Hok) as H.
    rewrite <- Heff in H. exact H.
  - intro o. rewrite HU. split.
    + intros (r & Hok & Ht).
      exists (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                            (brk_unmaps r (vm_brk (m_vmmaps model))) [] []),
             (brk_model (ms_gpr ms 0) r model), [].
      split; [apply brk_ok_intro; [exact Hno | exact Hok] | exact Ht].
    + intros (eff & model' & evs & Hspec & Ht).
      apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hspec.
      destruct Hspec as (_ & _ & Hok & _).
      exists (eff_ret eff). auto.
Qed.

(* [comment removed for export] *)
Lemma tou_wexit_eq : forall ms model bufs code,
  fd1chan model ->
  to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
  bufs_modeled bufs ->
  to_outcomes ms model (fun o => o = (bufs, code)).
Proof.
  intros ms model bufs code Hfd Hte Hbm.
  apply (tou_wexit ms model bufs code); [exact Hfd | exact Hte | exact Hbm | tauto].
Qed.

(* [comment removed for export] *)
Lemma tou_equiv : forall ms model U V,
  to_outcomes ms model U ->
  (forall o, V o <-> U o) ->
  to_outcomes ms model V.
Proof.
  intros ms model U V Hto; revert V.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros V HV.
  - apply (tou_wexit ms model bufs code); [exact Hfd | exact Hte | exact Hbm |].
    intro o. rewrite (HV o). apply HU.
  - eapply tou_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
  - apply (tou_brk ms model x8 T V); [exact Hsvc | exact Hno | |].
    + intros eff model' evs Hspec. exact (Hcont eff model' evs Hspec).
    + intro o. rewrite (HV o). apply HU.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma alloc_omni_run : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_outcomes (run_segments segs inp sp mb)
              (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
              (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                 (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) U ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (outcomes_post (in_fs inp) U).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto.
  cbn [omni_run]. unfold init_config.
  exact (to_outcomes_exec (run_segments segs inp sp mb) _ _ U Hto eq_refl eq_refl).
Qed.

Lemma alloc_obs_iff : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_outcomes (run_segments segs inp sp mb)
              (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
              (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                 (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) U ->
  forall tr, obs_trace (run_segments segs inp sp mb)
               (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
    <-> exists o, U o /\ is_prefix tr (outcome_trace (in_fs inp) o).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto tr.
  unfold init_config.
  set (ms := init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) in *.
  set (m0 := with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
               (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) in *.
  assert (Hh : m_halted m0 = None) by reflexivity.
  assert (Hlazy : m_vm_lazy m0 = []) by reflexivity.
  assert (Hfs : m_fs m0 = in_fs inp) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (to_outcomes_star_only (run_segments segs inp sp mb) ms _ U Hto Hh Hlazy tr' c Hstar)
      as (o & Ho & Hp').
    exists o. split; [exact Ho|].
    rewrite Hfs in Hp'. eapply is_prefix_trans; eauto.
  - intros (o & Ho & Hp).
    destruct (to_outcomes_star_admits (run_segments segs inp sp mb) ms _ U Hto Hh Hlazy o Ho) as [c Hstar].
    rewrite Hfs in Hstar.
    exists (outcome_trace (in_fs inp) o), c. split; assumption.
Qed.

Lemma alloc_no_error_run : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_outcomes (run_segments segs inp sp mb)
              (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
              (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                 (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) U ->
  ~ reaches_error (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto. apply exec_no_error.
  eapply exec_conseq; [exact (alloc_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto) |].
  intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma alloc_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp,
  to_outcomes (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp source_alloc_limit inp)) U ->
  to_outcomes (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp target_alloc_limit inp)) U ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp
    Hsource Htarget.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (alloc_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource) |].
    intros tr o (out & _ & _ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).
    rewrite (alloc_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (alloc_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget).
Qed.

(* [comment removed for export] *)
Lemma alloc_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         U inp,
  to_outcomes (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp rlim inp)) U ->
  to_outcomes (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp alim inp)) U ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    U inp Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    apply (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).
    rewrite (alloc_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).
    reflexivity.
  - cbn. apply (alloc_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget).
Qed.
End WithFP1.

End AllocSim.
From Stdlib Require NArith ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
Module MmapSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_MmapSim () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsCeq_rewrite_relationI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes;EquivalenceEpointwise_equivalenceC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:Proper_mapc59OSSVerify5KrLib7Mh_00387CatExec=flat_map_app'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00387CatExec9skipn_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_00387CatExec>flat_map_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00387WallSim:u_len_wordC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7div_posK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedC49OSSVerify5KrLib8PropExec6v_srliC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr07K47Corelib4Init9Datatypes4prod01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepc59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01c59OSSVerify5KrLib7Mh_00387SeqExec7step_sbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387SeqExecEN_to_le_bytes_1_smallC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib7Mh_00387MmapSim;step_sb_anyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec:word_add_0C1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC47Corelib4Init3Nat3addC49OSSVerify5KrLib8PropExecEnat_to_word_add_mergeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C49OSSVerify5KrLib8PropExec9word1_natC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00c59OSSVerify5KrLib7Mh_00388AllocSim8zmem_outC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib7Mh_00388AllocSim<rdn_zmem_outC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib7Mh_00306CatSim7fd1chanC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedK4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01C4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC46Stdlib5Lists4List6filterc59OSSVerify5KrLib7Mh_00387MmapSim<munmap_modelC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properc59OSSVerify5KrLib7Mh_00387MmapSim8grant_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC47Corelib7Classes9MorphismsFreflexive_proper_proxyC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses=iff_ReflexiveC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprc59OSSVerify5KrLib7Mh_00387MmapSim<mmap_args_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC56Stdlib6ZArith6BinInt1Z4landC49OSSVerify5KrLib8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_flags_coreC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi=MAP_ANONYMOUSC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_READC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi:PROT_WRITEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi;MAP_PRIVATEC47Corelib7Classes?RelationClasses;reflexivityI4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome00C5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch:lookup_armC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7sa_specC4ELinuxProcessSemantics?LinuxProcessSem5Monad9unmodeledC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;munmap_specC4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC59OSSVerify5KrLib7Mh_00307ExitSimBin_sysno_sys_inputC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specI4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7SpecArm00C5ELinuxProcessSemantics?LinuxProcessSem3Sys<SyscallTable:spec_tablec59OSSVerify5KrLib7Mh_00387MmapSim>munmap_args_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim=page_round_upC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap<check_munmapC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C47Corelib4Init9Datatypes3orbC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>munmap_free_okC47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasC4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEI6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03c59OSSVerify5KrLib7Mh_00387MmapSim:munmap_effC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01c59OSSVerify5KrLib7Mh_00387MmapSimCsyscall_spec_munmapC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=listNN_eqb_eqC49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSimDmunmap_check_modeledC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapEcheck_munmap_sound_okC47Corelib4Init5Logic5proj1C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapHcheck_munmap_complete_okC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapOcheck_munmap_complete_unmodeledC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap9mmap_specC46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude9errnos_okC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude?errnos_ok_rangeC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosc59OSSVerify5KrLib7Mh_00387MmapSimBmmap_args_ok_gatesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSimAsyscall_spec_mmapC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_in_introC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapCcheck_mmap_sound_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C4ELinuxProcessSemantics?LinuxProcessSem5State6EEXISTc59OSSVerify5KrLib7Mh_00387MmapSim?grant_ok_unpackC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>alloc_top_roomK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_in_belowC4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC4ELinuxProcessSemantics?LinuxProcessSem5StateBstack_max_size_valK46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib7Mh_00387MmapSim:mmap_modelC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapFpage_round_up_Z_nonnegc59OSSVerify5KrLib7Mh_00387MmapSim?grant_not_errnoC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapFcheck_mmap_complete_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextI47Corelib4Init5Logic2ex00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAerrno_ret_in_trueK47Corelib4Init5Logic2ex01C46Stdlib4Bool4Bool<andb_false_rC46Stdlib4Bool4Bool<andb_false_lC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapMcheck_mmap_complete_unmodeledc59OSSVerify5KrLib7Mh_00388AllocSim?apply_zeros_oneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosc59OSSVerify5KrLib7Mh_00387MmapSim5zfillC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcI47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z6leb_gtc59OSSVerify5KrLib7Mh_00387MmapSim6unfillC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc59OSSVerify5KrLib7Mh_00387MmapSim:unfill_outC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C46Stdlib4Bool4Bool;orb_false_rC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7existsbC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityI59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00387MmapSim3twm00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387MmapSim3twm04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:msteps_indC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00387MmapSim3twm20C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387MmapSim3twm23C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesI47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef5skipnC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0c59OSSVerify5KrLib7Mh_00387CatExec7adv_setC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387MmapSim3twm11C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387MmapSim3twm02C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387MmapSim3twm22C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim:adv_munmapC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387MmapSim3twm03C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andc59OSSVerify5KrLib7Mh_00387SeqExec>land_255_smallC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387MmapSim3twm01C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03c59OSSVerify5KrLib7Mh_00387MmapSim=munmap_ok_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesc59OSSVerify5KrLib7Mh_00387MmapSimDmunmap_model_no_lazyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedK4ELinuxProcessSemantics?LinuxProcessSem5State5event03c59OSSVerify5KrLib7Mh_00387MmapSimCmunmap_model_haltedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event04C4ELinuxProcessSemantics?LinuxProcessSem5StateIm_killed_of_m_halted_nonec59OSSVerify5KrLib7Mh_00387MmapSimCmunmap_no_unmodeledC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List7map_appC46Stdlib5Lists4List<firstn_skipnC59OSSVerify5KrLib7Mh_00306CatSim<bufs_modeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim8twm_postC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec00C59OSSVerify5KrLib7Mh_00306CatSim;buf_modeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim=twm_rest_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00307ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedC59OSSVerify5KrLib7Mh_00307ExitSim@exit_dispatch_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_killed_with_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep06C59OSSVerify5KrLib7Mh_00307ExitSim>sstep_exit_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_halted_with_haltedC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC59OSSVerify5KrLib7Mh_00306CatSim7weventsC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exits_withK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun>exec_step_onlyi59OSSVerify5KrLib7Mh_00387MmapSim3twm10C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C46Stdlib5Lists4List9app_assocC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_conseqc59OSSVerify5KrLib7Mh_00387MmapSimDmunmap_model_fd1chanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim9munmap_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04c59OSSVerify5KrLib7Mh_00387MmapSim@sstep_munmap_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim?munmap_model_fsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01C59OSSVerify5KrLib7Mh_00307ExitSim?sstep_instr_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC56Stdlib5Arith8PeanoNat3Nat7le_reflC59OSSVerify5KrLib7Mh_00306CatSim;write1_ok_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim?sstep_write_invC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome02C59OSSVerify5KrLib7Mh_00306CatSimAbuf_modeled_skipnC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes?RelationClassesEEquivalence_ReflexiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9Morphisms?eq_proper_proxyK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec02c59OSSVerify5KrLib7Mh_00387MmapSim:twm_mutindC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome00c59OSSVerify5KrLib7Mh_00387MmapSim<twm_exec_mutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim8twm_execC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_realizesI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun5mexec00I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun?mexec_halt_starC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun9exec_stari59OSSVerify5KrLib7Mh_00387MmapSim3tmw00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387MmapSim3tmw02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim>adv_mmap_grantC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387MmapSim3tmw01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim;mmap_ok_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSimEapply_effect_no_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim?mmap_model_lazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSimAmmap_model_haltedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSimAmmap_no_unmodeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim8tmw_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim<mmap_fail_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim>sstep_mmap_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSimBmmap_model_fd1chanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim=mmap_model_fsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim7tmw_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSimEENOMEM_in_mmap_errnosC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim?twm_star_admitsC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run4star02c59OSSVerify5KrLib7Mh_00387MmapSim<mmap_succ_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim8tmw_execC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSim:two_tracesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunGexits_with_never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_no_errorC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exec_soundc59OSSVerify5KrLib7Mh_00387MmapSimDtmw_star_admits_succC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSimDtmw_star_admits_failC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem3Run9obs_tracec59OSSVerify5KrLib7Mh_00387MmapSim=tmw_star_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387MmapSimHtwo_traces_prefix_closedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00c59OSSVerify5KrLib7Mh_00387MmapSim<tmw_no_errorC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=reaches_errorC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun8omni_runC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<img_segmentsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:omni_corunC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence:omni_equivc59OSSVerify5KrLib7Mh_00387MmapSim@mmap_omni_run_teC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_coexecC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunDnever_errors_coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=coexec_conseqC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence@omni_trace_equivC4ELinuxProcessSemantics?LinuxProcessSem3Run3runC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalenceDtrace_equiv_iff_omnic59OSSVerify5KrLib7Mh_00387MmapSim?mmap_obs_iff_teC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=bh_errors_iffc59OSSVerify5KrLib7Mh_00387MmapSimDmmap_no_error_run_teC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence7modeledC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence5equivC59OSSVerify5KrLib7Mh_00266SimInvDno_error_run_modeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=bh_all_errors".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_srli_div : forall (x : word) (sh : Z), (0 <= sh < 64)%Z ->
  bv_unsigned (v_srli x sh) = (bv_unsigned x / 2 ^ sh)%Z.
Proof.
  intros x sh Hsh. unfold v_srli.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (u64_range x) as Hx.
  assert (Hp : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hle : (bv_unsigned x / 2 ^ sh <= bv_unsigned x)%Z)
    by (apply Z.div_le_upper_bound; nia).
  assert (H0 : (0 <= bv_unsigned x / 2 ^ sh)%Z) by (apply Z.div_pos; lia).
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma step_sb_any : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            [Z_to_bv 8 (bv_unsigned (getr regs rs2))]) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  rewrite <- N_to_le_bytes_1_small.
  apply (step_sb segs regs pc mem rom w rs1 rs2 imm); assumption.
Qed.

(* [comment removed for export] *)
Lemma step_sb_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12)
                          (a v : word) (b : byte),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  Z_to_bv 8 (bv_unsigned v) = b ->
  RiscvSemantics.store_ok segs mem a 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v b Hf He Hd Ha Hv Hb Hok.
  rewrite (step_sb_any segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv, Hb. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_snoc : forall (bs : list byte) (m : word -> option byte)
                           (a : word) (b : byte),
  wbytes m a (bs ++ [b]) = wbytes (wbytes m a bs) (a + nat_to_word (length bs)) [b].
Proof.
  induction bs as [|x bs IH]; intros m a b.
  - cbn [app wbytes length]. rewrite word_add_0. reflexivity.
  - cbn [app wbytes length].
    rewrite IH. f_equal.
    rewrite word1_nat, nat_to_word_add_merge. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
  zmem m a n.

Lemma zfill_out : forall a n m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  zfill a n m x = m x.
Proof. intros a n m x Hx. exact (zmem_out m a n x Hx). Qed.

(* [comment removed for export] *)
Lemma rdn_zfill_out : forall segs a n m (x : word) k,
  (bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
  (bv_unsigned x + Z.of_nat k <= bv_unsigned a
   \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  rdn segs (zfill a n m) x k = rdn segs m x k.
Proof.
  intros segs a n m x k Hnw Hd. exact (rdn_zmem_out segs m a n x k Hnw Hd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m.

Lemma iv_subtract_outside : forall (b s : word) lo hi,
  (0 < bv_unsigned s)%Z -> (lo < hi)%Z ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z ->
  iv_subtract b s lo hi = [(b, s)].
Proof.
  intros b s lo hi Hs Hlh Hd. unfold iv_subtract. cbv zeta.
  destruct Hd as [Hd|Hd].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.max_l by lia.
    replace (bv_unsigned b + bv_unsigned s - bv_unsigned b)%Z
      with (bv_unsigned s) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_exact : forall l (a n : word),
  (0 < bv_unsigned n)%Z ->
  (forall b s, In (b, s) l -> (0 < bv_unsigned s)%Z) ->
  (forall b s, In (b, s) l -> b = a -> s = n) ->
  (forall b s, In (b, s) l -> b <> a ->
     (bv_unsigned b + bv_unsigned s <= bv_unsigned a
      \/ bv_unsigned a + bv_unsigned n <= bv_unsigned b)%Z) ->
  maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
  = map_remove l a.
Proof.
  induction l as [|[b s] r IH]; intros a n Hn Hpos Hu Hd; [reflexivity|].
  assert (IHr : maps_subtract r (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
                = map_remove r a).
  { apply IH; [exact Hn
              | intros b' s' H; apply (Hpos b' s'); right; exact H
              | intros b' s' H; apply (Hu b' s'); right; exact H
              | intros b' s' H; apply (Hd b' s'); right; exact H]. }
  cbn [maps_subtract]. rewrite IHr.
  unfold map_remove. cbn [List.filter fst]. fold (map_remove r a).
  destruct (bv_eqb b a) eqn:E; cbn [negb].
  - apply bv_eqb_eq in E. subst b.
    rewrite (Hu a s (or_introl eq_refl) eq_refl).
    unfold iv_subtract. cbv zeta.
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a))).
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a + bv_unsigned n))).
    reflexivity.
  - assert (Hne : b <> a) by (intros ->; rewrite bv_eqb_refl in E; discriminate).
    rewrite (iv_subtract_outside b s); [reflexivity | | lia |].
    + exact (Hpos b s (or_introl eq_refl)).
    + exact (Hd b s (or_introl eq_refl) Hne).
Qed.

Definition mmap_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
               ((a, n) :: vm_maps (m_vmmaps m))
               (vm_noaccess (m_vmmaps m))
               (vm_start_brk (m_vmmaps m))
               (vm_brk (m_vmmaps m))
               (vm_limit (m_vmmaps m))
               (vm_mmap_base (m_vmmaps m))
               (vm_init_sp (m_vmmaps m))) m.

(* [comment removed for export] *)
Definition page_round_up (len : word) : word :=
  Z_to_bv 64 (page_round_up_Z (bv_unsigned len)).

(* [comment removed for export] *)
Definition grant_ok (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a
  && (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.

Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma munmap_model_fs : forall addr n m, m_fs (munmap_model addr n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma munmap_model_fd1chan : forall addr n m, fd1chan m -> fd1chan (munmap_model addr n m).
Proof. intros addr n m H. exact H. Qed.
Lemma munmap_model_no_lazy : forall addr n m,
  m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
  intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
    vm_forget_range, with_vm_backing, with_vmmaps.
  cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
Lemma mmap_model_halted : forall a n m, m_halted (mmap_model a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mmap_model_fs : forall a n m, m_fs (mmap_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma mmap_model_fd1chan : forall a n m, fd1chan m -> fd1chan (mmap_model a n m).
Proof. intros a n m H. exact H. Qed.
Lemma mmap_model_lazy : forall a n m,
  m_vm_lazy (mmap_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma grant_ok_unpack : forall hint m a n,
  grant_ok hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true /\
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z.
Proof.
  intros hint m a n H. unfold grant_ok in H.
  rewrite !andb_true_iff in H.
  destruct H as [[[[[_ H1] H2] H3] H4] H5].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  apply Z.leb_le in H5.
  auto 7.
Qed.

Lemma grant_ok_place : forall hint m a n,
  grant_ok hint m a n = true ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof.
  intros hint m a n H. unfold grant_ok in H.
  rewrite !andb_true_iff in H. tauto.
Qed.

Lemma region_free_cons : forall (b s : word) r (lo n : word),
  region_free ((b, s) :: r) lo n = true ->
  (bv_unsigned lo + bv_unsigned n <= bv_unsigned b
   \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo)%Z
  /\ region_free r lo n = true.
Proof.
  intros b s r lo n H. cbn [region_free] in H.
  apply andb_true_iff in H. destruct H as [H1 H2].
  split; [|exact H2].
  apply negb_true_iff in H1. unfold iv_overlap in H1.
  apply andb_false_iff in H1.
  destruct H1 as [H1 | H1]; [right | left]; apply Z.ltb_ge in H1; lia.
Qed.

(* [comment removed for export] *)
Lemma source_alloc_limit_val : source_alloc_limit = 0x400000000%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma target_alloc_limit_val : target_alloc_limit = 0x8000000000%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma in_arg3_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3.
Proof. reflexivity. Qed.

Lemma in_arg4_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4.
Proof. reflexivity. Qed.

Lemma in_arg5_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition mmap_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)
Lemma mmap_args_ok_gates : forall ms,
  mmap_args_ok ms ->
  mmap_off_aligned_b (ms_gpr ms 5) = true /\
  mmap_anon_b (ms_gpr ms 3) = true /\
  w_is0 (ms_gpr ms 1) = false /\
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)
  = true.
Proof.
  intros ms (H1 & H2 & H3 & H4 & H5).
  split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
  split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
  unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
  (bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
  ms_gpr ms 1 <> Z_to_bv 64 0 /\
  (bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <= TASK_SIZE)%Z /\
  map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
    (page_round_up (ms_gpr ms 1)) = true.

(* [comment removed for export] *)
Definition munmap_eff (ms : machine_state) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] [].

(* [comment removed for export] *)
(* A munmap answers 0, which is not -ENOMEM, so it is never a refusal. *)
Lemma munmap_eff_ret_not_ENOMEM : forall ms,
  bv_eqb (eff_ret (munmap_eff ms)) (errno_ret ENOMEM) = false.
Proof. intros ms. unfold munmap_eff. vm_compute. reflexivity. Qed.

Lemma syscall_spec_munmap : forall segs ms x8 model o,
  bv_unsigned x8 = 215%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma munmap_check_modeled : forall ms model eff,
  munmap_args_ok ms model ->
  check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in munmap_errnos r
        then match us with
             | [] => CheckOk model []
             | _ => CheckReject
             end
        else if w_is0 r
                && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
        then CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms model eff (Hal & Hlen & Hnw & Hhas).
  unfold check_munmap.
  rewrite (proj2 (Z.eqb_eq _ _) Hal).
  unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
  cbn [negb orb]. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _) Hnw). cbv beta iota.
  unfold page_round_up in Hhas. rewrite Hhas. reflexivity.
Qed.

Lemma munmap_ok : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (munmap_eff ms)
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model Hno Ha.
  apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
  rewrite (munmap_check_modeled ms model _ Ha).
  unfold munmap_eff, w_is0.
  replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false by reflexivity.
  cbv beta iota. rewrite bv_eqb_refl.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma munmap_fail_ok : forall segs ms x8 model e,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  In e munmap_errnos ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
  intros segs ms x8 model e Hno Ha HIn.
  apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
  rewrite (munmap_check_modeled ms model _ Ha).
  rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.

Lemma ENOMEM_in_munmap_errnos : In ENOMEM munmap_errnos.
Proof. left. reflexivity. Qed.

Lemma munmap_ok_inv : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\
  ((exists e, In e munmap_errnos /\
     eff = mkEffect (errno_ret e) [] [] /\ model' = model)
   \/ (eff = munmap_eff ms /\
       model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
  apply check_munmap_complete_ok in Hspec.
  rewrite (munmap_check_modeled ms model eff Ha) in Hspec.
  destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
    [destruct zs as [|? ?]|]; try discriminate.
  destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
  destruct (errno_ret_in munmap_errnos r) eqn:He.
  - destruct us as [|? ?]; [|discriminate].
    inversion Hspec; clear Hspec; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    split; [reflexivity|]. left. exists e. auto.
  - destruct (w_is0 r
              && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))])
      eqn:HC; [|discriminate].
    inversion Hspec; clear Hspec; subst.
    apply andb_true_iff in HC as [Hr Hus].
    unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
    apply listNN_eqb_eq in Hus; subst us.
    split; [reflexivity|]. right. unfold munmap_eff. auto.
Qed.

Lemma munmap_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno Ha Hspec.
  apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_munmap_complete_unmodeled _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  rewrite (munmap_check_modeled ms model _ Ha) in Hspec.
  replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false in Hspec
    by reflexivity.
  cbv beta iota in Hspec.
  destruct (w_is0 (Z_to_bv 64 0)
            && listNN_eqb [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]);
    discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma syscall_spec_mmap : forall segs ms x8 model o,
  bv_unsigned x8 = 222%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> mmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
         (ms_gpr ms 4) (ms_gpr ms 5) (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

Lemma ENOMEM_in_mmap_errnos : In ENOMEM mmap_errnos.
Proof. left. reflexivity. Qed.

Lemma mmap_errno_range : forall e,
  In e mmap_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. intros e HIn. exact (errnos_ok_range mmap_errnos e eq_refl HIn). Qed.

Lemma place_declined_b_null : forall kb h nZ,
  place_declined_b kb h (Z_to_bv 64 0) nZ = false.
Proof.
  intros kb h nZ. unfold place_declined_b.
  replace (hint_address (Z_to_bv 64 0)) with 0%Z by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* [place_declined_b] premise and proof ported by name from
   727298f3:theories/Common/MmapSim.v (lemma [mmap_fail_ok]).  #146 put the
   decline ahead of the [alt] in [check_mmap]'s [mmap_modeled_b] arm
   (727298f3:theories/LinuxProcessSem/Checks/Sys/Mm/Mmap.v:104-109), so this
   producer must say the decline did not fire.  The recorded KReplay proof it
   replaces predates that arm. *)
Lemma mmap_fail_ok : forall segs ms x8 model e,
  bv_unsigned x8 = 222%Z -> mmap_args_ok ms -> In e mmap_errnos ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
  intros segs ms x8 model e Hno Ha HIn Hdecl.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite Hdecl.
  rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_not_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok hint model a n = true ->
  errno_ret_in mmap_errnos a = false.
Proof.
  intros hint model a n Hn Hg.
  destruct (grant_ok_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
  apply errno_ret_in_below; [reflexivity|].
  alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

Lemma mmap_succ_ok : forall segs ms x8 model a,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model a Hno Ha Hdecl Hg.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite Hdecl.
  rewrite (grant_not_errno (ms_gpr ms 0) model a
             (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
    [ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
      | exact Hg ].
  unfold grant_ok in Hg. rewrite !andb_true_iff in Hg.
  destruct Hg as [[[[[Hp H1] H2] H3] H4] H5].
  rewrite Hflags.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
    by (vm_compute; reflexivity).
  unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite Hnr.
  rewrite Hp, H5.
  unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
  reflexivity.
Qed.

Lemma grant_ok_intro : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true ->
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z ->
  grant_ok hint m a n = true.
Proof.
  intros hint m a n Hn Hnal Hpl Hbud.
  destruct (linux_place_is_admissible _ _ _ _ _ Hn Hnal Hpl)
    as (Hal & Hpos & Htop & Hfree).
  unfold grant_ok. rewrite Hpl, Hfree.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
    (proj2 (Z.leb_le _ _) Htop), (proj2 (Z.leb_le _ _) Hbud).
  reflexivity.
Qed.

Lemma mmap_ok_inv : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\ eff = mkEffect (errno_ret e) [] []
      /\ model' = model) \/
   (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
      /\ eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]
      /\ model' = mmap_model a (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply check_mmap_complete_ok in Hspec.
  unfold check_mmap in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  destruct (place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
              (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) eqn:Hdecl;
    [discriminate|].
  rewrite Hflags in Hspec.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
    by (vm_compute; reflexivity).
  unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
  rewrite Hnr in Hspec.
  destruct eff as [r ws zs us cs copyins].
  cbv beta iota zeta in Hspec.
  destruct ws as [|w ws]; [|discriminate].
  destruct us as [|u us]; [|discriminate].
  destruct cs as [|c cs]; [|discriminate].
  destruct copyins as [|copyin copyins]; [|discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:Herr; rewrite ?Herr in Hspec;
    cbv beta iota in Hspec.
  - destruct zs as [|z zs]; [|discriminate].
    inversion Hspec; subst.
    split; [reflexivity|]. left.
    apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
    exists e. auto.
  - destruct (linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
                (ms_gpr ms 0) (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) r
              && (vm_backing_used model
                  + page_round_up_Z (bv_unsigned (ms_gpr ms 1))
                  <=? vm_limit (m_vmmaps model))%Z) eqn:Hcond;
      rewrite ?Hcond in Hspec.
    2:{ rewrite andb_false_l in Hspec. discriminate. }
    destruct (listNN_eqb zs
                [(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]) eqn:Hzs;
      rewrite ?Hzs in Hspec.
    2:{ rewrite andb_false_r in Hspec. discriminate. }
    cbn [andb] in Hspec.
    apply listNN_eqb_eq in Hzs. subst zs.
    inversion Hspec; subst.
    split; [reflexivity|]. right.
    exists r. split; [|split].
    + apply andb_true_iff in Hcond as [Hpl Hbud].
      apply (grant_ok_intro _ _ _ _ (proj1 (mmap_grant_len_ok _ Hl))
               (proj2 (mmap_grant_len_ok _ Hl)) Hpl).
      now apply Z.leb_le.
    + unfold page_round_up. reflexivity.
    + reflexivity.
Qed.

(* Ported by name from 727298f3:theories/Common/MmapSim.v, [mmap_no_unmodeled].
   The `rewrite Hdecl in Hspec` MUST stay above the `cbv beta iota zeta in
   Hspec`: after the cbv the decline is folded into the match and the closing
   `destruct b` binds it instead of the gate the proof means. *)
Lemma mmap_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno Ha Hdecl Hspec.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_mmap in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  rewrite Hdecl in Hspec.
  cbv beta iota zeta in Hspec.
  assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
  rewrite E in Hspec. cbv beta iota in Hspec.
  match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
    discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_mmap_grant : forall regs pc sv mem rom a n,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (mkEffect a [] [(a, n)]))
  = mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom.
Proof.
  intros regs pc sv mem rom a n.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_writes apply_copies].
  unfold mkst, regupd.
  rewrite b_npc4, Hm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition unfill (a n : word) (m : word -> option byte) : word -> option byte :=
  fun x => if Z.leb (bv_unsigned a) (bv_unsigned x)
              && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n)
           then None else m x.

Lemma unfill_out : forall a n m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  unfill a n m x = m x.
Proof.
  intros a n m x Hx. unfold unfill.
  destruct Hx as [Hx | Hx].
  - rewrite (proj2 (Z.leb_gt (bv_unsigned a) (bv_unsigned x))) by lia. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned x) (bv_unsigned a + bv_unsigned n))) by lia.
    rewrite andb_false_r. reflexivity.
Qed.

Lemma rdn_unfill_out : forall segs a n m (x : word) k,
  (bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
  (bv_unsigned x + Z.of_nat k <= bv_unsigned a
   \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  rdn segs (unfill a n m) x k = rdn segs m x k.
Proof.
  intros segs a n m x k Hnw Hd. apply rdn_ext; [exact Hnw|].
  intros y Hy. apply unfill_out. lia.
Qed.

(* [comment removed for export] *)
Lemma adv_munmap : forall regs pc sv mem rom a n,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a n mem) rom.
Proof.
  intros regs pc sv mem rom a n.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) []
               = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd.
  rewrite b_npc4, Hm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Inductive twm : machine_state -> Model -> list (list byte) -> word -> Prop :=
| twm_exit : forall ms model x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    twm ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twm_write : forall ms model buf bufs code,
    (1 <= length buf)%nat ->
    twm_pend ms model buf bufs code ->
    twm ms model (buf :: bufs) code
| twm_munmap : forall ms model x8 bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 215%Z ->
    munmap_args_ok ms model ->
    (forall e, In e munmap_errnos ->
       twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bufs code) ->
    twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
    twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm ms' model bufs code ->
    twm ms model bufs code
(** The put-style retry loop realizing one buffer: a write-pending state
    offering the remainder [rest]; the environment delivers any nonempty
    prefix, the loop reissues on the rest.  The trace contribution of the
    whole node is exactly the FULL buffer (WallSim's [to_wall] shape,
    inlined here because the continuation is the mutual [twm]). *)
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       twm_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model
         (skipn n rest) bufs code) ->
    twm_pend ms model rest bufs code
with twm_tail : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmt_done : forall ms model bufs code,
    twm ms model bufs code ->
    twm_tail ms model [] bufs code
| twmt_more : forall ms model rest bufs code,
    (1 <= length rest)%nat ->
    twm_pend ms model rest bufs code ->
    twm_tail ms model rest bufs code
| twmt_step : forall ms ms' model rest bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm_tail ms' model rest bufs code ->
    twm_tail ms model rest bufs code.

Scheme twm_min := Minimality for twm Sort Prop
  with twm_pend_min := Minimality for twm_pend Sort Prop
  with twm_tail_min := Minimality for twm_tail Sort Prop.
Combined Scheme twm_mutind from twm_min, twm_pend_min, twm_tail_min.

Lemma msteps_twm : forall ms ms' model bufs code,
  msteps segs ms ms' -> twm ms' model bufs code -> twm ms model bufs code.
Proof.
  intros ms ms' model bufs code H; induction H; [auto|].
  intro Hw. eapply twm_step; eauto.
Qed.

Lemma msteps_twm_tail : forall ms ms' model rest bufs code,
  msteps segs ms ms' -> twm_tail ms' model rest bufs code ->
  twm_tail ms model rest bufs code.
Proof.
  intros ms ms' model rest bufs code H; induction H; [auto|].
  intro Hw. eapply twmt_step; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma twm_write_ret : forall regs pc mem rom model buf bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some buf ->
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     twm_tail (mkst (regupd regs 10 (len_word (firstn n buf))) (v_addi pc 4) mem rom)
       model (skipn n buf) bufs code) ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model (buf :: bufs) code.
Proof.
  intros regs pc mem rom model buf bufs code H17 H10 Hr Hok Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  apply twm_write; [exact Hnb|].
  eapply twmp_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
Lemma twm_tail_write_rec : forall regs pc mem rom model rest bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some rest ->
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length rest)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
     twm_tail (mkst (regupd regs 10 (len_word (firstn n rest))) (v_addi pc 4) mem rom)
       model (skipn n rest) bufs code) ->
  twm_tail {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
              ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
              ms_mem := mem; ms_rom := rom |}
    model rest bufs code.
Proof.
  intros regs pc mem rom model rest bufs code H17 H10 Hr Hok Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  apply twmt_more; [exact Hnb|].
  eapply twmp_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
Lemma twm_munmap_rec : forall regs pc mem rom model bufs code (a nlen : word),
  bv_unsigned (getr regs 17) = 215%Z ->
  reg_get regs 10 = a ->
  reg_get regs 11 = nlen ->
  (bv_unsigned a mod page_size = 0)%Z ->
  nlen <> Z_to_bv 64 0 ->
  (bv_unsigned a + page_round_up_Z (bv_unsigned nlen) <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (page_round_up nlen) = true ->
  (forall e, In e munmap_errnos ->
     twm (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom)
         model bufs code) ->
  twm (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
            (unfill a (page_round_up nlen) mem) rom)
      (munmap_model a (page_round_up nlen) model) bufs code ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model bufs code.
Proof.
  intros regs pc mem rom model bufs code a nlen H17 Ha Hn Hal Hlen Hnw Hhas Hfail Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  eapply twm_munmap.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold munmap_args_ok, ms_gpr. cbn [ms_regs].
    rewrite E10, E11, Ha, Hn. auto.
  - intros e He. rewrite adv_set. exact (Hfail e He).
  - unfold munmap_eff, ms_gpr. cbn [ms_regs].
    rewrite E10, E11, Ha, Hn.
    rewrite adv_munmap. exact Hcont.
Qed.

(* [comment removed for export] *)
Lemma twm_exit_coden : forall regs pc mem rom model (c : word),
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = c -> (bv_unsigned c < 256)%Z ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model [] c.
Proof.
  intros regs pc mem rom model c H17 H10 Hc.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (Hg : bv_and (ms_gpr {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                                 ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                                 ms_mem := mem; ms_rom := rom |} 0)
                      (Z_to_bv 64 255) = c).
  { unfold ms_gpr. cbn [ms_regs]. rewrite E10, H10.
    apply land_255_small. exact Hc. }
  rewrite <- Hg.
  eapply twm_exit.
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_munmap_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e munmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                     (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (-> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + right.
      match goal with
      | Hmat : materialize_model_accesses
          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _
          (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
        inversion Hmat; subst
      end.
      reflexivity.
  - (* sstep_syscall_materialization_fault: no lazy range can fault *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & -> & ->) | (-> & ->)];
      [ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy _ _
          (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat ];
      discriminate
    end.
  - (* sstep_exit : munmap leaves haltedness unchanged *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite Hh in H6
      | rewrite munmap_model_halted, Hh in H6 ];
      discriminate
    end.
  - (* sstep_killed : munmap leaves it unkilled for the same reason *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6
      | rewrite m_killed_of_m_halted_none in H6;
        [| rewrite munmap_model_halted; exact Hh] ];
      discriminate
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition twm_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
  fun tr o => tr = wevents bufs ++ [ExitEv code fs] /\ exits_with code tr o.

Definition twm_rest_post (rest : list byte) (bufs : list (list byte)) (code : word)
    (fs : Fs.Fs) : post :=
  fun tr o => tr = map (WriteEv (Z_to_bv 64 1)) rest ++ wevents bufs ++ [ExitEv code fs]
              /\ exits_with code tr o.

Lemma twm_exec_mut :
  (forall ms model bufs code, twm ms model bufs code ->
     bufs_modeled bufs ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)))
  /\ (forall ms model rest bufs code, twm_pend ms model rest bufs code ->
     buf_modeled rest -> bufs_modeled bufs ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
  /\ (forall ms model rest bufs code, twm_tail ms model rest bufs code ->
     buf_modeled rest -> bufs_modeled bufs ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model))).
Proof.
  apply (twm_mutind
    (fun ms model bufs code =>
       bufs_modeled bufs ->
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)))
    (fun ms model rest bufs code =>
       buf_modeled rest -> bufs_modeled bufs ->
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
    (fun ms model rest bufs code =>
       buf_modeled rest -> bufs_modeled bufs ->
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))).
  - (* twm_exit *)
    intros ms model x8 Hsvc Hx8 Hbm Hh Hlazy Hfd.
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold twm_post. cbn beta. rewrite app_nil_r. cbn [wevents app]. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* twm_write: the wall node contributes the full buffer *)
    intros ms model buf bufs code Hnb Hp IH Hbm Hh Hlazy Hfd.
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    eapply exec_conseq; [exact (IH Hb Hbs Hh Hlazy Hfd) |].
    intros tr o (Heq & Hx). split; [| exact Hx].
    rewrite Heq. cbn [wevents]. rewrite <- app_assoc. reflexivity.
  - (* twm_munmap: the refusal and the cut *)
    intros ms model x8 bufs code Hsvc Hno Hargs Hfail IHfail Hcut IH Hbm Hh Hlazy Hfd.
    assert (Hh' : m_halted
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = None)
      by (rewrite munmap_model_halted; exact Hh).
    assert (Hfd' : fd1chan
                     (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))
      by (apply munmap_model_fd1chan; exact Hfd).
    apply exec_step; [exact Hh | | |].
    + eexists; eexists.
      apply (sstep_syscall segs ms model x8 (munmap_eff ms)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
      * exact Hh.
      * exact Hsvc.
      * apply munmap_ok; [exact Hno | exact Hargs].
      * exact Hh'.
      * apply materialize_model_accesses_no_lazy.
        exact (munmap_model_no_lazy _ _ _ Hlazy).
    + intros evs Hss.
      destruct (sstep_munmap_inv ms model x8 evs SError Hh Hlazy Hsvc Hno Hargs Hss)
        as (_ & [(e & _ & Habs) | Habs]); discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_munmap_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hargs Hss)
        as (-> & [(e & He & Hc) | Hc]); injection Hc as ->.
      * eapply exec_conseq; [exact (IHfail e He Hbm Hh Hlazy Hfd) |].
        intros tr o (Heq & Hx). split; [| exact Hx].
        cbn [app]. exact Heq.
      * eapply exec_conseq;
          [exact (IH Hbm Hh' (munmap_model_no_lazy _ _ _ Hlazy) Hfd') |].
        intros tr o (Heq & Hx). split; [| exact Hx].
        cbn [app]. rewrite Heq, munmap_model_fs. reflexivity.
  - (* twm_step *)
    intros ms ms' model bufs code Hsvc Hstep Hte IH Hbm Hh Hlazy Hfd.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
  - (* twmp_write: every delivered length is a successor *)
    intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbr Hbm Hh Hlazy Hfd.
    apply exec_step; [exact Hh | | |].
    + eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length rest)]
                  (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
               (map (WriteEv (Z_to_bv 64 1)) (firstn (length rest) rest))).
      * exact Hh.
      * exact Hsvc.
      * apply write1_ok_n; try assumption. apply Nat.le_refl.
      * exact Hh.
      * apply materialize_model_accesses_no_lazy. exact Hlazy.
    + intros evs Hss.
      destruct (sstep_write_inv segs ms model x8 rest evs SError
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbr Hnb Hss) as (n & _ & _ & _ & Habs).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_write_inv segs ms model x8 rest evs (SNext c')
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbr Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
      injection Hc' as ->.
      eapply exec_conseq;
        [exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbr) Hbm Hh Hlazy Hfd) |].
      intros tr o (Heq & Hx). split; [| exact Hx].
      rewrite Heq. rewrite <- (firstn_skipn n rest) at 3.
      rewrite map_app, <- !app_assoc. reflexivity.
  - (* twmt_done *)
    intros ms model bufs code Hte IH Hbr Hbm Hh Hlazy Hfd.
    eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |].
    intros tr o (Heq & Hx). split; [| exact Hx]. cbn [map app]. exact Heq.
  - (* twmt_more *)
    intros ms model rest bufs code Hnb Hp IH Hbr Hbm Hh Hlazy Hfd.
    exact (IH Hbr Hbm Hh Hlazy Hfd).
  - (* twmt_step *)
    intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hbr Hbm Hh Hlazy Hfd.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbr Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
Qed.

Lemma twm_exec : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)).
Proof. intros ms model bufs code Hte. exact (proj1 twm_exec_mut ms model bufs code Hte). Qed.

Lemma twm_star_admits : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  exists c, star segs (mkCfg ms model) (wevents bufs ++ [ExitEv code (m_fs model)]) c.
Proof.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd.
  destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

Lemma twm_star_only : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    is_prefix tr (wevents bufs ++ [ExitEv code (m_fs model)]).
Proof.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) Hstar))
    as (tr' & o & _ & Heq & _).
  rewrite <- Heq. apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tmw : machine_state -> Model -> list (list byte) -> word
                -> list (list byte) -> word -> Prop :=
| tmw_mmap : forall ms model x8 bf cf bs cs,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 222%Z ->
    mmap_args_ok ms ->
    place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
      (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
    (forall e, In e mmap_errnos ->
       twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf) ->
    (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
       twm (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
           (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
    (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
    tmw ms model bf cf bs cs
| tmw_step : forall ms ms' model bf cf bs cs,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    tmw ms' model bf cf bs cs ->
    tmw ms model bf cf bs cs.

Lemma msteps_tmw : forall ms ms' model bf cf bs cs,
  msteps segs ms ms' -> tmw ms' model bf cf bs cs -> tmw ms model bf cf bs cs.
Proof.
  intros ms ms' model bf cf bs cs H; induction H; [auto|].
  intro Hw. eapply tmw_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma tmw_mmap_rec : forall regs pc mem rom model bf cf bs cs,
  bv_unsigned (getr regs 17) = 222%Z ->
  reg_get regs 11 <> Z_to_bv 64 0 ->
  reg_get regs 12 = Z_to_bv 64 3 ->
  reg_get regs 13 = Z_to_bv 64 34 ->
  reg_get regs 14 = Z_to_bv 64 (-1) ->
  reg_get regs 15 = Z_to_bv 64 0 ->
  place_declined_b (m_kernel model) (m_vmmaps model) (reg_get regs 10)
    (page_round_up_Z (bv_unsigned (reg_get regs 11))) = false ->
  (forall e, In e mmap_errnos ->
     twm (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model bf cf) ->
  (forall a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true ->
     twm (mkst (regupd regs 10 a) (v_addi pc 4)
               (zfill a (page_round_up (reg_get regs 11)) mem) rom)
         (mmap_model a (page_round_up (reg_get regs 11)) model) bs cs) ->
  (exists a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true) ->
  tmw {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model bf cf bs cs.
Proof.
  intros regs pc mem rom model bf cf bs cs H17 H11 H12 H13 H14 H15
    Hdecl Hfail Hsucc Hex.
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  assert (E13 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg)) by (apply bv_eq; reflexivity).
  assert (E14 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg)) by (apply bv_eq; reflexivity).
  assert (E15 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg)) by (apply bv_eq; reflexivity).
  eapply tmw_mmap.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold mmap_args_ok, ms_gpr. cbn [ms_regs].
    rewrite E11, E12, E13, E14, E15.
    auto.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11. exact Hdecl.
  - intros e HIn. rewrite adv_set. apply Hfail; assumption.
  - intros a Hg. rewrite adv_mmap_grant.
    unfold ms_gpr in *. cbn [ms_regs] in *. rewrite E11 in *.
    apply Hsucc. exact Hg.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11. exact Hex.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_mmap_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
      st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model)))).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hdecl Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (a & Hg & -> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + match goal with
      | Hmat : materialize_model_accesses (mmap_model a _ model) _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _
          (eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat;
        inversion Hmat; subst
      end.
      right. exists a. auto.
  - (* sstep_syscall_materialization_fault: no lazy range can fault *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy _ _
          (eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat ];
      discriminate
    end.
  - (* sstep_exit *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite Hh in H6; discriminate
      | rewrite mmap_model_halted, Hh in H6; discriminate ]
    end.
  - (* sstep_killed: the same two shapes, through
       [State.m_killed_of_m_halted_none] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(e & _ & _ & Hm) | (a & _ & _ & Hm)]; subst model';
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
      | assert (Hhn : m_halted
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model) = None)
          by (rewrite mmap_model_halted; exact Hh);
        rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate ]
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (mmap_no_unmodeled segs ms x8 model Hno Hargs Hdecl H3)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tmw_post (bf : list (list byte)) (cf : word) (bs : list (list byte)) (cs : word)
    (fs : Fs.Fs) : post :=
  fun tr o => (tr = wevents bf ++ [ExitEv cf fs] /\ exits_with cf tr o)
              \/ (tr = wevents bs ++ [ExitEv cs fs] /\ exits_with cs tr o).

Lemma tmw_exec : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  OmniRun.exec segs (mkCfg ms model) (tmw_post bf cf bs cs (m_fs model)).
Proof.
  intros ms model bf cf bs cs Hte.
  induction Hte as
    [ms model x8 bf cf bs cs Hsvc Hno Hargs Hdecl Hfail Hsucc Hex
    | ms ms' model bf cf bs cs Hsvc Hstep Hte IH];
    intros Hbf Hbs Hh Hlazy Hfd.
  - (* tmw_mmap: the errno branches and the grants are exactly the successors *)
    apply exec_step; [exact Hh | | |].
    + eexists; eexists.
      apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret ENOMEM) [] []) model model []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_fail_ok; [exact Hno | exact Hargs | apply ENOMEM_in_mmap_errnos | exact Hdecl].
      * exact Hh.
      * apply materialize_model_accesses_no_lazy. exact Hlazy.
    + intros evs Hss.
      destruct (sstep_mmap_inv ms model x8 evs SError Hh Hlazy Hsvc Hno Hargs Hdecl Hss)
        as (_ & [(e & _ & Habs) | (a & _ & Habs)]); discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_mmap_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hargs Hdecl Hss)
        as (-> & [(e & He & Hc') | (a & Hg & Hc')]); injection Hc' as ->.
      * (* failure: the first straight line *)
        eapply exec_conseq; [exact (twm_exec _ _ _ _ (Hfail e He) Hbf Hh Hlazy Hfd) |].
        intros tr o (Heq & Hx). left. split; [cbn [app]; exact Heq | exact Hx].
      * (* success: the second, at the mapped model *)
        set (n := page_round_up (ms_gpr ms 1)) in *.
        assert (Hh' : m_halted (mmap_model a n model) = None)
          by (rewrite mmap_model_halted; exact Hh).
        assert (Hfd' : fd1chan (mmap_model a n model))
          by (apply mmap_model_fd1chan; exact Hfd).
        eapply exec_conseq;
          [exact (twm_exec _ _ _ _ (Hsucc a Hg) Hbs Hh'
                    (eq_trans (mmap_model_lazy _ _ _) Hlazy) Hfd') |].
        intros tr o (Heq & Hx). right. split; [| exact Hx].
        cbn [app]. rewrite Heq, mmap_model_fs. reflexivity.
  - (* tmw_step *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbf Hbs Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
Qed.

Lemma tmw_star_admits_fail : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bf ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  exists c, star segs (mkCfg ms model) (wevents bf ++ [ExitEv cf (m_fs model)]) c.
Proof.
  intros ms model bf cf bs cs Hte.
  induction Hte as
    [ms model x8 bf cf bs cs Hsvc Hno Hargs Hdecl Hfail Hsucc Hex
    | ms ms' model bf cf bs cs Hsvc Hstep Hte IH]; intros Hbm Hh Hlazy Hfd.
  - destruct (twm_star_admits _ _ _ _ (Hfail ENOMEM ENOMEM_in_mmap_errnos)
                Hbm Hh Hlazy Hfd) as [c Hstar].
    rewrite <- apply_effect_no_write in Hstar.
    exists c.
    replace (wevents bf ++ [ExitEv cf (m_fs model)])
      with ([] ++ (wevents bf ++ [ExitEv cf (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret ENOMEM) [] [])
             model model []).
    + exact Hh.
    + exact Hsvc.
    + apply mmap_fail_ok; [exact Hno | exact Hargs | apply ENOMEM_in_mmap_errnos | exact Hdecl].
    + exact Hh.
    + apply materialize_model_accesses_no_lazy. exact Hlazy.
  - destruct (IH Hbm Hh Hlazy Hfd) as [c Hstar].
    exists c.
    replace (wevents bf ++ [ExitEv cf (m_fs model)])
      with ([] ++ (wevents bf ++ [ExitEv cf (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma tmw_star_admits_succ : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  exists c, star segs (mkCfg ms model) (wevents bs ++ [ExitEv cs (m_fs model)]) c.
Proof.
  intros ms model bf cf bs cs Hte.
  induction Hte as
    [ms model x8 bf cf bs cs Hsvc Hno Hargs Hdecl Hfail Hsucc Hex
    | ms ms' model bf cf bs cs Hsvc Hstep Hte IH]; intros Hbm Hh Hlazy Hfd.
  - destruct Hex as [a Hg].
    set (n := page_round_up (ms_gpr ms 1)) in *.
    assert (Hh' : m_halted (mmap_model a n model) = None)
      by (rewrite mmap_model_halted; exact Hh).
    assert (Hfd' : fd1chan (mmap_model a n model))
      by (apply mmap_model_fd1chan; exact Hfd).
    destruct (twm_star_admits _ _ _ _ (Hsucc a Hg) Hbm Hh'
                (eq_trans (mmap_model_lazy _ _ _) Hlazy) Hfd') as [c Hstar].
    rewrite mmap_model_fs in Hstar.
    exists c.
    replace (wevents bs ++ [ExitEv cs (m_fs model)])
      with ([] ++ (wevents bs ++ [ExitEv cs (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
             (mmap_model a n model) (mmap_model a n model) []).
    + exact Hh.
    + exact Hsvc.
    + apply mmap_succ_ok; [exact Hno | exact Hargs | exact Hdecl | exact Hg].
    + exact Hh'.
    + apply materialize_model_accesses_no_lazy.
      exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
  - destruct (IH Hbm Hh Hlazy Hfd) as [c Hstar].
    exists c.
    replace (wevents bs ++ [ExitEv cs (m_fs model)])
      with ([] ++ (wevents bs ++ [ExitEv cs (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
Definition two_traces (bf : list (list byte)) (cf : word)
    (bs : list (list byte)) (cs : word)
    (fs : Fs.Fs) (tr : list event) : Prop :=
  is_prefix tr (wevents bf ++ [ExitEv cf fs]) \/
  is_prefix tr (wevents bs ++ [ExitEv cs fs]).

Lemma tmw_star_only : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    two_traces bf cf bs cs (m_fs model) tr.
Proof.
  intros ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (tmw_exec ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) Hstar))
    as (tr' & o & _ & [(Heq & _) | (Heq & _)]); [left | right];
    rewrite <- Heq; apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tmw_no_error : forall ms model bf cf bs cs,
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  tmw ms model bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model bf cf bs cs Hh Hlazy Hfd Hte Hbf Hbs. apply exec_no_error.
  eapply exec_conseq; [exact (tmw_exec ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) |].
  intros tr o [(_ & Hx) | (_ & Hx)]; exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma twm_exec_not_errors : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  ~ OmniRun.exec segs (mkCfg ms model) OmniRun.errors.
Proof.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd Hex.
  destruct (exec_realizes _ _ _ Hex) as (tr & o & Hm & Herr).
  destruct (exec_sound _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) _ _ Hm)
    as (_ & Hx).
  exact (exits_with_never_errors _ _ _ Hx Herr).
Qed.

Lemma twm_exec_code_unique : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  forall code', OmniRun.exec segs (mkCfg ms model) (exits_with code') -> code' = code.
Proof.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd code' Hex.
  destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
    as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as ->. reflexivity.
Qed.

Lemma tmw_exec_not_errors : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  ~ OmniRun.exec segs (mkCfg ms model) OmniRun.errors.
Proof.
  intros ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd Hex.
  destruct (exec_realizes _ _ _ Hex) as (tr & o & Hm & Herr).
  destruct (exec_sound _ _ _ (tmw_exec ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) _ _ Hm)
    as [(_ & Hx) | (_ & Hx)]; exact (exits_with_never_errors _ _ _ Hx Herr).
Qed.

(* [comment removed for export] *)
Lemma tmw_exec_not_fail_only : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  ~ is_prefix (wevents bs ++ [ExitEv cs (m_fs model)]) (wevents bf ++ [ExitEv cf (m_fs model)]) ->
  ~ OmniRun.exec segs (mkCfg ms model) (twm_post bf cf (m_fs model)).
Proof.
  intros ms model bf cf bs cs Hte Hbs Hh Hlazy Hfd Hnp Hex.
  destruct (tmw_star_admits_succ ms model bf cf bs cs Hte Hbs Hh Hlazy Hfd) as (c & Hstar).
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ Hex Hstar)) as (tr' & o & _ & Heq & _).
  apply Hnp. rewrite <- Heq. apply is_prefix_app.
Qed.

Lemma tmw_exec_not_succ_only : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bf ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  ~ is_prefix (wevents bf ++ [ExitEv cf (m_fs model)]) (wevents bs ++ [ExitEv cs (m_fs model)]) ->
  ~ OmniRun.exec segs (mkCfg ms model) (twm_post bs cs (m_fs model)).
Proof.
  intros ms model bf cf bs cs Hte Hbf Hh Hlazy Hfd Hnp Hex.
  destruct (tmw_star_admits_fail ms model bf cf bs cs Hte Hbf Hh Hlazy Hfd) as (c & Hstar).
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ Hex Hstar)) as (tr' & o & _ & Heq & _).
  apply Hnp. rewrite <- Heq. apply is_prefix_app.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma two_traces_prefix_closed : forall bf cf bs cs fs tr tr',
  two_traces bf cf bs cs fs tr -> is_prefix tr' tr -> two_traces bf cf bs cs fs tr'.
Proof.
  intros bf cf bs cs fs tr tr' [H | H] Hp;
    [left | right]; eapply is_prefix_trans; eauto.
Qed.

Lemma mmap_obs_iff_te : forall segs pc ph sp brk0 mb rnd lim inp bf cf bs cs,
  tmw segs (init_machine_state segs pc ph sp mb rnd inp)
      (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
         (init_model (segments_reserved segs) brk0 mb sp lim inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> two_traces bf cf bs cs (in_fs inp) tr.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs Hr tr.
  unfold init_config in *.
  set (ms := init_machine_state segs pc ph sp mb rnd inp) in *.
  set (m0 := with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
               (init_model (segments_reserved segs) brk0 mb sp lim inp)) in *.
  assert (Hh : m_halted m0 = None) by reflexivity.
  assert (Hlazy : m_vm_lazy m0 = []) by reflexivity.
  assert (Hfd : fd1chan m0)
    by exact (init_model_fd1chan (segments_reserved segs) brk0 mb sp lim inp Hr).
  assert (Hfs : m_fs m0 = in_fs inp) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    pose proof (tmw_star_only segs ms _ bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd
                  tr' c Hstar) as H2.
    rewrite Hfs in H2.
    eapply two_traces_prefix_closed; eauto.
  - intros [Hp | Hp].
    + destruct (tmw_star_admits_fail segs ms _ bf cf bs cs Hte Hbf Hh Hlazy Hfd)
        as [c Hstar].
      rewrite Hfs in Hstar.
      exists (wevents bf ++ [ExitEv cf (in_fs inp)]), c. split; assumption.
    + destruct (tmw_star_admits_succ segs ms _ bf cf bs cs Hte Hbs Hh Hlazy Hfd)
        as [c Hstar].
      rewrite Hfs in Hstar.
      exists (wevents bs ++ [ExitEv cs (in_fs inp)]), c. split; assumption.
Qed.

Lemma mmap_no_error_run_te : forall segs pc ph sp brk0 mb rnd lim inp bf cf bs cs,
  tmw segs (init_machine_state segs pc ph sp mb rnd inp)
      (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
         (init_model (segments_reserved segs) brk0 mb sp lim inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs Hr.
  unfold init_config.
  apply (tmw_no_error segs _
           (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved segs) brk0 mb sp lim inp)) bf cf bs cs);
    [reflexivity | reflexivity
    | exact (init_model_fd1chan (segments_reserved segs) brk0 mb sp lim inp Hr)
    | exact Hte | exact Hbf | exact Hbs].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mmap_omni_run_te : forall segs pc ph sp brk0 mb rnd lim inp bf cf bs cs,
  tmw (run_segments segs inp sp mb)
      (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
      (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
         (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (tmw_post bf cf bs cs (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs Hr.
  cbn [omni_run]. unfold init_config.
  exact (tmw_exec (run_segments segs inp sp mb) _ _ bf cf bs cs Hte Hbf Hbs eq_refl eq_refl
           (init_model_fd1chan (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp
              Hr)).
Qed.

Lemma mmap_omni_strong_equiv_te :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp,
  tmw (run_segments source_segs inp rsp rmb)
      (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
      (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
         (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
            source_alloc_limit inp)) bf cf bs cs ->
  tmw (run_segments target_segs inp asp amb)
      (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
      (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
         (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
            target_alloc_limit inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp
    Hsource Htarget Hbf Hbs Hr.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (mmap_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bf cf bs cs
                Hsource Hbf Hbs Hr) |].
    intros tr o [(_ & Hx) | (_ & Hx)];
      exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (mmap_obs_iff_te (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd
               source_alloc_limit inp bf cf bs cs
               Hsource Hbf Hbs Hr tr).
    rewrite (mmap_obs_iff_te (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd
               target_alloc_limit inp bf cf bs cs
               Htarget Hbf Hbs Hr tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (mmap_no_error_run_te (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd
             target_alloc_limit inp bf cf bs cs
             Htarget Hbf Hbs Hr).
Qed.

Lemma mmap_strong_equiv_te :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp,
  tmw (run_segments source_segs inp rsp rmb)
      (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
      (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
         (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
            rlim inp)) bf cf bs cs ->
  tmw (run_segments target_segs inp asp amb)
      (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
      (with_vdso (Vdso.vdso_run_init (ed_vdso arnd))
         (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
            alim inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp
    Hsource Htarget Hbf Hbs Hr.
  split.
  { apply no_error_run_modeled.
    apply (mmap_no_error_run_te (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd
             rlim inp bf cf bs cs
             Hsource Hbf Hbs Hr). }
  right. split.
  - intro tr. cbn.
    rewrite (mmap_obs_iff_te (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd
               rlim inp bf cf bs cs
               Hsource Hbf Hbs Hr tr).
    rewrite (mmap_obs_iff_te (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd
               alim inp bf cf bs cs
               Htarget Hbf Hbs Hr tr).
    reflexivity.
  - cbn. apply (mmap_no_error_run_te (run_segments target_segs inp asp amb) apc aph asp abrk amb
                  arnd alim inp bf cf bs cs
                  Htarget Hbf Hbs Hr).
Qed.
End WithFP1.

End MmapSim.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run OmniRun.
Module AllocSim2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Vdso Run OmniRun.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim.

Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition two_outcomes (bf : list (list byte)) (cf : word)
    (bs : list (list byte)) (cs : word)
    : (list (list byte) * word) -> Prop :=
  fun o => o = (bf, cf) \/ o = (bs, cs).

(* [comment removed for export] *)
Lemma alloc_mmap_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp,
  to_outcomes (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (StackLayout.ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
          rlim inp))
    (two_outcomes bf cf bs cs) ->
  tmw (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (StackLayout.ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
          alim inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs
    inp Hsource Htarget Hbf Hbs Hr.
  split.
  { apply no_error_run_modeled.
    apply (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp
             (two_outcomes bf cf bs cs) Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp
               (two_outcomes bf cf bs cs) Hsource tr).
    rewrite (mmap_obs_iff_te (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd
               alim inp
               bf cf bs cs Htarget Hbf Hbs Hr tr).
    unfold two_traces, two_outcomes, outcome_trace.
    split.
    + intros (o & [-> | ->] & Hp); cbn [fst snd] in Hp; [left | right]; exact Hp.
    + intros [Hp | Hp]; [exists (bf, cf) | exists (bs, cs)];
        cbn [fst snd]; auto.
  - cbn.
    apply (mmap_no_error_run_te (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd
             alim inp
             bf cf bs cs Htarget Hbf Hbs Hr).
Qed.

(* [comment removed for export] *)
Lemma alloc_mmap_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp,
  to_outcomes (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (Vdso.vdso_run_init (StackLayout.ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
          source_alloc_limit inp))
    (two_outcomes bf cf bs cs) ->
  tmw (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (Vdso.vdso_run_init (StackLayout.ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
          target_alloc_limit inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs
    inp Hsource Htarget Hbf Hbs Hr.
  apply strong_equiv_iff.
  apply (alloc_mmap_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit
           target_segs apc aph asp abrk amb arnd target_alloc_limit bf cf bs cs inp
           Hsource Htarget Hbf Hbs Hr).
Qed.

End AllocSim2.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
Module FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_FPSteps () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsCeq_rewrite_relationI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes;EquivalenceEpointwise_equivalenceC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:Proper_mapc59OSSVerify5KrLib7Mh_00387CatExec=flat_map_app'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00387CatExec9skipn_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_00387CatExec>flat_map_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00387WallSim:u_len_wordC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv3Fpu;fflags_bitsK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic3and01K4ELinuxProcessSemantics5Riscv3Fpu6fflags01C4ELinuxProcessSemantics5Riscv3Fpu5fl_nxC4ELinuxProcessSemantics5Riscv3Fpu5fl_ufC4ELinuxProcessSemantics5Riscv3Fpu5fl_ofC4ELinuxProcessSemantics5Riscv3Fpu5fl_dzC4ELinuxProcessSemantics5Riscv3Fpu5fl_nvC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I4ELinuxProcessSemantics5Riscv3Fpu6fflags00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes:comparison01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z;land_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula05C49OSSVerify5KrLib8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_specC49OSSVerify5KrLib8PropExecAZ_bounded_by_bitsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z8lor_specC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib7Mh_00387FPSteps8frm_zeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387FPSteps<fp_u32_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7lor_0_rK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z:shiftr_lorc59OSSVerify5KrLib7Mh_00387FPSteps>fp_Z_lor_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387FPSteps;fp_u_Z2bv32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lnotc59OSSVerify5KrLib7Mh_00387FPStepsAfp_Z_land_range_lC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z8land_0_rC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z9land_m1_rC56Stdlib6ZArith6BinInt1Z;shiftr_landC56Stdlib6ZArith6BinInt1Z:shiftl_0_rC4ELinuxProcessSemantics5Riscv3Sem9slice_setI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics5Riscv3Fpu:rmode_of_ZK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic3notK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics5Riscv3Fpu>rmode_of_fieldI47Corelib4Init5Logic2ex00K46Stdlib9micromega5Tauto8GFormula07I4ELinuxProcessSemantics5Riscv3Fpu5rmode00K46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv3Fpu5rmode01K4ELinuxProcessSemantics5Riscv3Fpu5rmode02K4ELinuxProcessSemantics5Riscv3Fpu5rmode03K4ELinuxProcessSemantics5Riscv3Fpu5rmode04K4ELinuxProcessSemantics5Riscv3Fpu5rmode05K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr0IK47Corelib4Init9Datatypes4prod01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib8PropExec7FPState01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics5Riscv3Sem5is_x0C49OSSVerify5KrLib8PropExec=bv_eqb0_is_x0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC49OSSVerify5KrLib8PropExec6ov_rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr4ffmt02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics5Riscv3Sem7nan_boxK4ELinuxProcessSemantics5Riscv5Instr4ffmt01K4ELinuxProcessSemantics5Riscv5Instr5instr0JC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memc59OSSVerify5KrLib7Mh_00387CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32K4ELinuxProcessSemantics5Riscv5Instr5instr0RC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr6fmvdir01K4ELinuxProcessSemantics5Riscv5Instr6fmvdir02K4ELinuxProcessSemantics5Riscv5Instr5instr0NC4ELinuxProcessSemantics5Riscv3Sem7unbox_sC4ELinuxProcessSemantics5Riscv3Sem8sgnj_valI4ELinuxProcessSemantics5Riscv5Instr6fsgnop00I4ELinuxProcessSemantics5Riscv5Instr4ffmt00K4ELinuxProcessSemantics5Riscv5Instr5instr0Lc59OSSVerify5KrLib7Mh_00387FPSteps=fp_resolve_rmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387FPStepsDfp_fflags_bits_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387FPStepsBfp_frm_zero_accrueC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem9fp_formatC4ELinuxProcessSemantics5Riscv3Fpu6fp_addC4ELinuxProcessSemantics5Riscv3Fpu6fp_subC4ELinuxProcessSemantics5Riscv3Fpu6fp_mulC4ELinuxProcessSemantics5Riscv3Fpu6fp_divK4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff02I4ELinuxProcessSemantics5Riscv5Instr6fariop00I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00K4ELinuxProcessSemantics5Riscv5Instr5instr0QC4ELinuxProcessSemantics5Riscv3Fpu:fp_convertC4ELinuxProcessSemantics5Riscv3Fpu9fp_of_intC4ELinuxProcessSemantics5Riscv3Fpu9fp_to_intI4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty00K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty05K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty06K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty01K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty02K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty03K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty04K4ELinuxProcessSemantics5Riscv5Instr5instr0PC4ELinuxProcessSemantics5Riscv3Fpu5fp_eqC4ELinuxProcessSemantics5Riscv3Fpu5fp_ltC4ELinuxProcessSemantics5Riscv3Fpu5fp_leI4ELinuxProcessSemantics5Riscv5Instr6fcmpop00K4ELinuxProcessSemantics5Riscv5Instr5instr0GC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics5Riscv3SemAcsr_write_illegalK4ELinuxProcessSemantics5Riscv3Sem3eff03C4ELinuxProcessSemantics5Riscv3Sem9csr_sliceC4ELinuxProcessSemantics5Riscv3Sem9slice_getC45stdpp9bitvector;definitions5bv_orK4ELinuxProcessSemantics5Riscv5Instr5csrop02K4ELinuxProcessSemantics5Riscv5Instr5instr0HC4ELinuxProcessSemantics5Riscv7Prelude4zextc59OSSVerify5KrLib7Mh_00387FPStepsDfp_frm_zero_slice0_5C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition frm_zero (f : bv 32) : Prop :=
  Z.land (Z.shiftr (bv_unsigned f) 5) 7 = 0%Z.

Lemma fp_frm_zero_fx0 : frm_zero (@fp_csr fx0).
Proof. reflexivity. Qed.

Lemma fp_fflags_bits_range : forall fl, (0 <= fflags_bits fl < 32)%Z.
Proof.
  intros [nv dz of_ uf nx]. unfold fflags_bits. cbn [fl_nx fl_uf fl_of fl_dz fl_nv].
  destruct nv, dz, of_, uf, nx; vm_compute; split; congruence.
Qed.

Lemma fp_u32_range : forall f : bv 32, (0 <= bv_unsigned f < 2^32)%Z.
Proof. intros f. pose proof (bv_unsigned_in_range _ f) as H. unfold bv_modulus in H. exact H. Qed.

Lemma fp_Z_land_range_l : forall n a b, (0 <= n)%Z -> (0 <= a < 2^n)%Z ->
  (0 <= Z.land a b < 2^n)%Z.
Proof.
  intros n a b Hn Ha. split; [apply Z.land_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.land_nonneg; lia |].
  intros k Hk. rewrite Z.land_spec. rewrite (Z_testbit_high n a k) by lia. reflexivity.
Qed.

Lemma fp_Z_lor_range : forall n a b, (0 <= n)%Z -> (0 <= a < 2^n)%Z -> (0 <= b < 2^n)%Z ->
  (0 <= Z.lor a b < 2^n)%Z.
Proof.
  intros n a b Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.lor_nonneg; lia |].
  intros k Hk. rewrite Z.lor_spec.
  rewrite (Z_testbit_high n a k) by lia. rewrite (Z_testbit_high n b k) by lia. reflexivity.
Qed.

Lemma fp_u_Z2bv32 : forall z, (0 <= z < 2^32)%Z -> bv_unsigned (Z_to_bv 32 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz.
Qed.

(* [comment removed for export] *)
Lemma fp_frm_zero_accrue : forall (f : bv 32) (b : Z),
  (0 <= b < 32)%Z -> frm_zero f ->
  frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned f) b)).
Proof.
  intros f b Hb Hf. unfold frm_zero in *.
  pose proof (fp_u32_range f) as Hr.
  rewrite fp_u_Z2bv32 by (apply (fp_Z_lor_range 32); lia).
  rewrite Z.shiftr_lor. rewrite (Z.shiftr_div_pow2 b 5) by lia.
  rewrite (Z.div_small b (2^5)) by lia. rewrite Z.lor_0_r. exact Hf.
Qed.

(* [comment removed for export] *)
Lemma fp_frm_zero_slice0_5 : forall (f : bv 32) (v : word),
  frm_zero f -> frm_zero (slice_set f 0 5 v).
Proof.
  intros f v Hf. unfold frm_zero, slice_set in *.
  pose proof (fp_u32_range f) as Hr.
  change (Z.shiftl (Z.ones 5) 0) with 31%Z.
  rewrite Z.shiftl_0_r.
  assert (H1 : (0 <= Z.land (bv_unsigned f) (Z.lnot 31) < 2^32)%Z)
    by (apply fp_Z_land_range_l; lia).
  assert (H2 : (0 <= Z.land (bv_unsigned v) 31 < 2^32)%Z).
  { split; [apply Z.land_nonneg; right; lia|].
    rewrite Z.land_comm. apply (proj2 (fp_Z_land_range_l 32 31 (bv_unsigned v) ltac:(lia) ltac:(lia))). }
  rewrite fp_u_Z2bv32 by (apply (fp_Z_lor_range 32); lia).
  rewrite Z.shiftr_lor, !Z.shiftr_land.
  change (Z.shiftr (Z.lnot 31) 5) with (-1)%Z. change (Z.shiftr 31 5) with 0%Z.
  rewrite Z.land_m1_r, Z.land_0_r, Z.lor_0_r. exact Hf.
Qed.

(* [comment removed for export] *)
Lemma fp_resolve_rm : forall (rm : bv 3) (f : bv 32),
  frm_zero f ->
  (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
  exists md, rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned f) 5) 7) = Some md.
Proof.
  intros rm f Hf Hrm. unfold rmode_of_field. rewrite Hf.
  pose proof (bv_unsigned_in_range _ rm) as Hr.
  destruct (Z.eqb_spec (bv_unsigned rm) 7) as [E|NE].
  - exists RNE. reflexivity.
  - unfold rmode_of_Z.
    destruct (Z.eqb_spec (bv_unsigned rm) 0); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 1); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 2); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 3); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 4); [eexists; reflexivity|].
    exfalso. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac fp_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val Sem.exec_csr
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.fget Sem.fset Sem.with_fregs Sem.with_fcsr Sem.fread Sem.fwrite
     Sem.accrue Sem.resolve_rm Sem.frm_of
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     RiscvSemantics.access_value RiscvSemantics.drop_access_report
     ms_regs ms_fregs ms_fcsr ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst fp_regs fp_csr];
  rewrite ?bv_eqb0_is_x0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fp_step_fld : forall (fx : FPState) segs regs pc mem rom w rd rs (imm : bv 12) a bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FLoad FMT_D rd rs imm, 4%Z) ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 8%nat = Some bs ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx))
                   regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs imm a bs Hf He Hd Ha Hr.
  fp_pipeline Hf He Hd.
  unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
  rewrite ov_rdn, b_addsext, Ha, Hr. cbv beta iota.
  cbn [fp_regs fp_csr]. rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fp_step_flw : forall (fx : FPState) segs regs pc mem rom w rd rs (imm : bv 12) a bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FLoad FMT_S rd rs imm, 4%Z) ->
  v_addi (getr regs rs) (bv_signed imm) = a ->
  rdn segs mem a 4%nat = Some bs ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (bv_extract 0 32 (le_bytes_to_word bs))) (@fp_regs fx)) (@fp_csr fx))
                   regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs imm a bs Hf He Hd Ha Hr.
  fp_pipeline Hf He Hd.
  unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
  rewrite ov_rdn, b_addsext, Ha, Hr. cbv beta iota.
  cbn [fp_regs fp_csr]. rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fp_step_fsd : forall (fx : FPState) segs regs pc mem rom w rs1 rs2 (imm : bv 12) a,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FStore FMT_D rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst fx regs (v_addi pc 4)
               (wbytes mem a (word_to_le_bytes 8 (reg_get (@fp_regs fx) rs2))) rom).
Proof.
  intros fx segs regs pc mem rom w rs1 rs2 imm a Hf He Hd Ha Hok.
  fp_pipeline Hf He Hd.
  unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
  rewrite b_addsext, Ha, Hok. cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4. destruct fx; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fp_step_fsw : forall (fx : FPState) segs regs pc mem rom w rs1 rs2 (imm : bv 12) a,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FStore FMT_S rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  store_ok segs mem a 4%nat = true ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst fx regs (v_addi pc 4)
               (wbytes mem a (Z_to_le_bytes 4 (bv_unsigned (low32 (reg_get (@fp_regs fx) rs2))))) rom).
Proof.
  intros fx segs regs pc mem rom w rs1 rs2 imm a Hf He Hd Ha Hok.
  fp_pipeline Hf He Hd.
  unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
  rewrite b_addsext, Ha, Hok. cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4. destruct fx; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fp_step_fmv_x_d : forall (fx : FPState) segs regs pc mem rom w rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_X_F FMT_D rd rs1, 4%Z) ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd (reg_get (@fp_regs fx) rs1))
               (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
  fp_pipeline Hf He Hd.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; destruct fx; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fp_step_fmv_x_w : forall (fx : FPState) segs regs pc mem rom w rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_X_F FMT_S rd rs1, 4%Z) ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst fx (if bv_eqb rd 0 then regs
                       else regupd regs rd (sext 64 (low32 (reg_get (@fp_regs fx) rs1))))
               (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
  fp_pipeline Hf He Hd.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; destruct fx; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fp_step_fmv_d_x : forall (fx : FPState) segs regs pc mem rom w rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_F_X FMT_D rd rs1, 4%Z) ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (getr regs rs1) (@fp_regs fx)) (@fp_csr fx))
               regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
  fp_pipeline Hf He Hd. unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fp_step_fmv_w_x : forall (fx : FPState) segs regs pc mem rom w rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_F_X FMT_S rd rs1, 4%Z) ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (low32 (getr regs rs1))) (@fp_regs fx)) (@fp_csr fx))
               regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
  fp_pipeline Hf He Hd. unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fp_step_fsgnj : forall (fx : FPState) segs regs pc mem rom w op fmt rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fsgnj op fmt rd rs1 rs2, 4%Z) ->
  exists fr',
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP fr' (@fp_csr fx)) regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w op fmt rd rs1 rs2 Hf He Hd.
  destruct fmt; eexists; fp_pipeline Hf He Hd; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fp_step_fari : forall (fx : FPState) segs regs pc mem rom w op fmt rd rs1 rs2 (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fari op fmt rd rs1 rs2 rm, 4%Z) ->
  frm_zero (@fp_csr fx) ->
  (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
  exists fr' cs',
    frm_zero cs' /\
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (mkFP fr' cs') regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w op fmt rd rs1 rs2 rm Hf He Hd Hz Hrm.
  destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
  destruct fx as [fr cs]. cbn [fp_csr] in *.
  assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
    by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
  fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
  repeat match goal with
         | |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
         end.
  destruct fmt; cbv beta iota; rewrite b_npc4;
    (eexists _, _; split; [apply Hacc | reflexivity]).
Qed.

(* [comment removed for export] *)
Lemma fp_step_fcvt_to_f : forall (fx : FPState) segs regs pc mem rom w dst src rd rs1 (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  (dst = FC_S \/ dst = FC_D) ->
  frm_zero (@fp_csr fx) ->
  (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
  exists fr' cs',
    frm_zero cs' /\
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (mkFP fr' cs') regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w dst src rd rs1 rm Hf He Hd Hdst Hz Hrm.
  destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
  destruct fx as [fr cs]. cbn [fp_csr] in *.
  assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
    by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
  fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct Hdst as [-> | ->]; destruct src; cbv beta iota;
    repeat match goal with
           | |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
           end;
    try (destruct (is_x0 rs1); cbv beta iota);
    repeat match goal with
           | |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
           end;
    rewrite b_npc4;
    (eexists _, _; split; [ | reflexivity ]; first [apply Hacc | exact Hz]).
Qed.

(* [comment removed for export] *)
Lemma fp_step_fcvt_to_x : forall (fx : FPState) segs regs pc mem rom w dst src rd rs1 (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  (dst = FC_W \/ dst = FC_WU \/ dst = FC_L \/ dst = FC_LU) ->
  (src = FC_S \/ src = FC_D) ->
  frm_zero (@fp_csr fx) ->
  (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
  exists (v : word) cs',
    frm_zero cs' /\
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (mkFP (@fp_regs fx) cs') (if bv_eqb rd 0 then regs else regupd regs rd v)
                 (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w dst src rd rs1 rm Hf He Hd Hdst Hsrc Hz Hrm.
  destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
    by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
  fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
  destruct Hdst as [-> | [-> | [-> | ->]]]; destruct Hsrc as [-> | ->]; cbv beta iota;
    repeat match goal with
           | |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
           end;
    (destruct (is_x0 rd); cbv beta iota; rewrite b_npc4;
     [ exists (Z_to_bv 64 0); eexists; split; [ apply Hacc | reflexivity ]
     | eexists _, _; split; [ apply Hacc | reflexivity ] ]).
Qed.

(* [comment removed for export] *)
Lemma fp_step_fcmp : forall (fx : FPState) segs regs pc mem rom w op fmt rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcmp op fmt rd rs1 rs2, 4%Z) ->
  frm_zero (@fp_csr fx) ->
  exists (b : bool) cs',
    frm_zero cs' /\
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (mkFP (@fp_regs fx) cs')
                 (if bv_eqb rd 0 then regs else regupd regs rd (if b then Z_to_bv 64 1 else Z_to_bv 64 0))
                 (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w op fmt rd rs1 rs2 Hf He Hd Hz.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
    by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
  fp_pipeline Hf He Hd.
  repeat match goal with
         | |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
         end.
  destruct (is_x0 rd);
    [ exists true; eexists; split; [ apply Hacc | rewrite b_npc4; reflexivity ]
    | exists v; destruct v; cbv beta iota; rewrite b_npc4;
      (eexists; split; [ apply Hacc | reflexivity ]) ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fp_step_frrm : forall (fx : FPState) segs regs pc mem rom w rd,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Csr CSR_RS rd 0 2, 4%Z) ->
  frm_zero (@fp_csr fx) ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0))
               (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd Hf He Hd Hz.
  destruct fx as [fr cs]. cbn [fp_csr] in Hz. unfold frm_zero in Hz.
  fp_pipeline Hf He Hd.
  change (csr_slice 2) with (Some (5%Z, 3%Z)). cbv beta iota.
  unfold slice_get. change (Z.ones 3) with 7%Z. rewrite Hz.
  change (is_x0 0) with true. cbv beta iota.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fp_step_csrsi_fflags : forall (fx : FPState) segs regs pc mem rom w (uimm : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (CsrI CSR_RS 0 uimm 1, 4%Z) ->
  frm_zero (@fp_csr fx) ->
  exists cs',
    frm_zero cs' /\
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (mkFP (@fp_regs fx) cs') regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w uimm Hf He Hd Hz.
  destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
  destruct (Z.eqb (bv_unsigned uimm) 0) eqn:Eu.
  - exists cs. split; [exact Hz|].
    fp_pipeline Hf He Hd. rewrite Eu.
    change (csr_slice 1) with (Some (0%Z, 5%Z)). cbv beta iota.
    change (is_x0 0) with true. cbv beta iota. rewrite b_npc4. reflexivity.
  - exists (slice_set cs 0 5 (bv_or (slice_get cs 0 5) (zext 64 uimm))).
    split; [apply fp_frm_zero_slice0_5; exact Hz|].
    fp_pipeline Hf He Hd. rewrite Eu.
    change (csr_slice 1) with (Some (0%Z, 5%Z)). cbv beta iota.
    change (is_x0 0) with true. cbv beta iota. rewrite b_npc4. reflexivity.
Qed.

End FPSteps.
From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
Module FrmKeep.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FRM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition csr_frm_unsafe (writes : bool) (csr : bv 12) : bool :=
  writes && ((bv_unsigned csr =? 2) || (bv_unsigned csr =? 3)).
Definition csr_writes (op : csrop) (nz : bool) : bool := match op with CSR_RW => true | _ => nz end.
Definition instr_frm_safe (i : instr) : bool :=
  match i with
  | Csr op rd rs1 csr => negb (csr_frm_unsafe (csr_writes op (negb (is_x0 rs1))) csr)
  | CsrI op rd uimm csr => negb (csr_frm_unsafe (csr_writes op (negb (Z.eqb (bv_unsigned uimm) 0))) csr)
  | _ => true
  end.
Definition word_frm_safe (w : bv 32) : bool :=
  match decode_any w with Some (i, _) => instr_frm_safe i | None => true end.

(* [comment removed for export] *)
Fixpoint eff_fz (e : eff) : Prop :=
  match e with
  | EDone c => frm_zero (c_fcsr c)
  | ELoad n a k => forall v, eff_fz (k v)
  | EStore n a v k => eff_fz k
  | _ => True
  end.

(* [comment removed for export] *)
Lemma fc_rset r v c : c_fcsr (rset r v c) = c_fcsr c.
Proof. unfold rset. destruct (is_x0 r); [reflexivity|]. destruct c; reflexivity. Qed.
Lemma fc_with_pc v c : c_fcsr (with_pc v c) = c_fcsr c. Proof. destruct c; reflexivity. Qed.
Lemma fc_with_resv v c : c_fcsr (with_resv v c) = c_fcsr c. Proof. destruct c; reflexivity. Qed.
Lemma fc_with_regs f c : c_fcsr (with_regs f c) = c_fcsr c. Proof. destruct c; reflexivity. Qed.
Lemma fc_with_fregs f c : c_fcsr (with_fregs f c) = c_fcsr c. Proof. destruct c; reflexivity. Qed.
Lemma fc_fset r v c : c_fcsr (fset r v c) = c_fcsr c. Proof. unfold fset. apply fc_with_fregs. Qed.
Lemma fc_fwrite fmt r v c : c_fcsr (fwrite fmt r v c) = c_fcsr c. Proof. unfold fwrite. destruct fmt; apply fc_fset. Qed.
Lemma fc_inval_resv a c : c_fcsr (inval_resv a c) = c_fcsr c.
Proof. unfold inval_resv. destruct (c_resv c) as [r0|]; [destruct (bv_unsigned r0 =? bv_unsigned a); [apply fc_with_resv| reflexivity]| reflexivity]. Qed.
Lemma fc_accrue fl c : c_fcsr (accrue fl c) = Z_to_bv 32 (Z.lor (bv_unsigned (c_fcsr c)) (fflags_bits fl)).
Proof. destruct c; reflexivity. Qed.
Lemma fz_accrue fl c : frm_zero (c_fcsr c) -> frm_zero (c_fcsr (accrue fl c)).
Proof. intros H. rewrite fc_accrue. apply fp_frm_zero_accrue; [apply fp_fflags_bits_range| exact H]. Qed.

Ltac fz_core FZ :=
  repeat first [ exact FZ
               | rewrite fc_rset | rewrite fc_with_pc | rewrite fc_with_resv | rewrite fc_with_regs | rewrite fc_fset
               | rewrite fc_fwrite | rewrite fc_inval_resv | apply fz_accrue ].

Ltac fz_tree FZ :=
  repeat first [ lazymatch goal with
                 | |- eff_fz (match ?x with _ => _ end) => destruct x
                 | |- eff_fz ((match ?x with _ => _ end) _) => destruct x
                 | |- eff_fz (EDone _) => cbn [eff_fz]
                 | |- eff_fz (ELoad _ _ _) => cbn [eff_fz]; intros ?
                 | |- eff_fz (EStore _ _ _ _) => cbn [eff_fz]
                 | |- eff_fz (exec_csr _ _ _ _ _ _) => fail
                 | |- eff_fz _ => exact I
                 | |- frm_zero (c_fcsr (match ?x with _ => _ end)) => destruct x
                 | |- frm_zero _ => progress (fz_core FZ)
                 end ].

(* [comment removed for export] *)
Lemma exec_csr_fz op rd operand writes csr c :
  frm_zero (c_fcsr c) -> csr_frm_unsafe writes csr = false -> eff_fz (exec_csr op rd operand writes csr c).
Proof.
  intros FZ SF. unfold exec_csr, csr_slice. cbv zeta. unfold csr_frm_unsafe in SF.
  destruct (Z.eqb_spec (bv_unsigned csr) 1) as [E1|N1].
  - cbn [eff_fz]. rewrite fc_rset. destruct writes; [| exact FZ]. apply fp_frm_zero_slice0_5. exact FZ.
  - destruct (Z.eqb_spec (bv_unsigned csr) 2) as [E2|N2].
    + destruct writes; [cbn in SF; rewrite ?E2 in SF; cbn in SF; discriminate|]. cbn [eff_fz]. rewrite fc_rset. exact FZ.
    + destruct (Z.eqb_spec (bv_unsigned csr) 3) as [E3|N3]; [| exact I].
      destruct writes; [cbn in SF; rewrite ?E3 in SF; cbn in SF; discriminate|]. cbn [eff_fz]. rewrite fc_rset. exact FZ.
Qed.

Lemma exec_fz (sz : word) (i : instr) (c : core) :
  frm_zero (c_fcsr c) -> instr_frm_safe i = true -> eff_fz (exec sz i c).
Proof.
  intros FZ SF. destruct i; cbv beta iota zeta delta [exec load_val store_val]; try (fz_tree FZ).
  - (* [comment removed for export] *) cbn [instr_frm_safe csr_writes] in SF. apply negb_true_iff in SF. apply exec_csr_fz; [fz_core FZ| exact SF].
  - (* [comment removed for export] *) cbn [instr_frm_safe csr_writes] in SF. apply negb_true_iff in SF. apply exec_csr_fz; [fz_core FZ| exact SF].
Qed.

(* [comment removed for export] *)
Lemma interp_fz segs : forall e m rep, eff_fz e -> interp_eff_accesses segs e m = MachineOk rep -> frm_zero (c_fcsr (fst (@access_value _ rep))).
Proof.
  induction e as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m rep FZ H; cbn [interp_eff_accesses] in H; try discriminate.
  - injection H as <-. exact FZ.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|lazymatch type of H with context [if ?b then _ else _] => destruct b end; discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r| | ] eqn:E; try discriminate.
    injection H as <-. cbn [access_value fst]. exact (IH _ m r (FZ _) E).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r| | ] eqn:E; try discriminate.
    injection H as <-. cbn [access_value fst]. exact (IH _ r FZ E).
Qed.

(* [comment removed for export] *)
Lemma decode_exec_fz segs st w rep :
  frm_zero (ms_fcsr st) -> word_frm_safe w = true -> decode_exec_accesses segs st w = MachineOk rep -> frm_zero (ms_fcsr (@access_value _ rep)).
Proof.
  intros FZ SF H. unfold decode_exec_accesses in H. unfold word_frm_safe in SF.
  destruct (is_ecall w); [injection H as <-; exact FZ|].
  destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
  destruct (interp_eff_accesses _ _) as [r| | ] eqn:E; try discriminate.
  pose proof (interp_fz segs _ _ r (exec_fz (Z_to_bv 64 isz) i (Core (ms_regs st) (ms_fregs st) (ms_pc_val st) (ms_fcsr st) (ms_resv st)) FZ SF) E) as FZ'.
  destruct (@access_value _ r) as [c m'] eqn:Er. cbv beta iota zeta in H. injection H as <-. cbn [access_value ms_fcsr fst] in *. exact FZ'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma find_segment_In : forall l a n seg, find_segment l a n = Some seg -> In seg l.
Proof.
  induction l as [|s l IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (_ && _); [injection H as <-; left; reflexivity| right; exact (IH _ _ _ H)].
Qed.
Lemma find_segment_range : forall l a n seg, find_segment l a n = Some seg ->
  Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction l as [|s l IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.leb_spec (Z.of_N (seg_base s)) a) as [L1|L1]; destruct (Z.leb_spec (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [L2|L2]; cbn [andb] in H;
    first [injection H as <-; split; assumption | exact (IH _ _ _ H)].
Qed.

Section Generic.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis no_wx : forall seg, In seg segs -> seg_executable seg && seg_writable seg = false.

Lemma code_read_ov_none m a n : code_read_ov segs m a n = None.
Proof.
  unfold code_read_ov. destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:E; [|reflexivity].
  rewrite (no_wx seg (find_segment_In _ _ _ _ E)). reflexivity.
Qed.
Lemma fetch_word_ov_none m a : fetch_word_ov segs m a = None.
Proof. unfold fetch_word_ov. rewrite code_read_ov_none. destruct (negb _); reflexivity. Qed.
Lemma fetch_half_any_eq m a : fetch_half_any segs m a = fetch_half segs a.
Proof. unfold fetch_half_any. destruct (fetch_half segs a); [reflexivity|]. unfold fetch_half_ov. rewrite code_read_ov_none. reflexivity. Qed.
Lemma fetch_tail_any_eq m a : fetch_tail_any segs m a = fetch_tail segs a.
Proof. unfold fetch_tail_any, fetch_tail. rewrite !fetch_half_any_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma code_read_seg a n bs : code_read segs a n = Some bs ->
  exists seg, In seg segs /\ seg_executable seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + Z.of_N n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  unfold code_read. destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:E; [|discriminate].
  destruct (seg_executable seg) eqn:X; [|discriminate]. intros _. exists seg.
  split; [exact (find_segment_In _ _ _ _ E)|]. split; [exact X|]. exact (find_segment_range _ _ _ _ E).
Qed.
Lemma fetch_word_seg a w : fetch_word segs a = Some w ->
  bv_unsigned a mod 2 = 0 /\ exists seg, In seg segs /\ seg_executable seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + 4 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  unfold fetch_word. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  destruct (code_read segs a 4) as [bs|] eqn:C; [|discriminate]. intros _. split; [exact E|]. exact (code_read_seg a 4 bs C).
Qed.
Lemma fetch_tail_seg a w : fetch_tail segs a = Some w ->
  bv_unsigned a mod 2 = 0 /\ exists seg, In seg segs /\ seg_executable seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + 2 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  unfold fetch_tail. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  unfold fetch_half at 1. destruct (code_read segs a 2) as [bs|] eqn:C; [|discriminate]. intros _. split; [exact E|]. exact (code_read_seg a 2 bs C).
Qed.

(* [comment removed for export] *)
Definition ok_at (a : Z) : bool :=
  (match fetch_word segs (Z_to_bv 64 a) with Some w => word_frm_safe w | None => true end)
  && (match fetch_tail segs (Z_to_bv 64 a) with Some w => word_frm_safe w | None => true end).
Fixpoint scan1 (f : nat) (a : Z) : bool := match f with O => true | S f' => ok_at a && scan1 f' (a + 2) end.
Fixpoint scan2 (g f : nat) (a : Z) : bool := match g with O => true | S g' => scan1 f a && scan2 g' f (a + 2 * Z.of_nat f) end.

Lemma scan1_sound : forall f a0, scan1 f a0 = true -> forall a, a0 <= a < a0 + 2 * Z.of_nat f -> (a - a0) mod 2 = 0 -> ok_at a = true.
Proof.
  induction f as [|f IH]; intros a0 H a Ha Hm; [cbn [Z.of_nat] in Ha; lia|].
  cbn [scan1] in H. apply andb_true_iff in H as [H0 H1].
  destruct (Z.eq_dec a a0) as [->|NE]; [exact H0|].
  apply (IH (a0 + 2) H1); [lia|]. replace (a - (a0 + 2)) with (a - a0 + (-1) * 2) by lia. rewrite Z.mod_add by lia. exact Hm.
Qed.
Lemma scan2_sound : forall g f a0, scan2 g f a0 = true -> forall a, a0 <= a < a0 + 2 * Z.of_nat f * Z.of_nat g -> (a - a0) mod 2 = 0 -> ok_at a = true.
Proof.
  induction g as [|g IH]; intros f a0 H a Ha Hm; [cbn [Z.of_nat] in Ha; lia|].
  cbn [scan2] in H. apply andb_true_iff in H as [H0 H1].
  destruct (Z_lt_le_dec a (a0 + 2 * Z.of_nat f)) as [LT|GE].
  - exact (scan1_sound f a0 H0 a ltac:(lia) Hm).
  - apply (IH f (a0 + 2 * Z.of_nat f) H1); [lia|]. replace (a - (a0 + 2 * Z.of_nat f)) with (a - a0 + (- Z.of_nat f) * 2) by lia.
    rewrite Z.mod_add by lia. exact Hm.
Qed.

(* [comment removed for export] *)
Theorem fetch_safe_of_scan (xlo xsz : Z) (g f : nat) :
  (forall seg, In seg segs -> seg_executable seg = true -> Z.of_N (seg_base seg) = xlo /\ Z.of_N (seg_size seg) = xsz) ->
  xlo mod 2 = 0 -> xsz <= 2 * Z.of_nat f * Z.of_nat g -> scan2 g f xlo = true ->
  forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> word_frm_safe w = true.
Proof.
  intros XS XE COV SC a w H.
  assert (R : bv_unsigned a mod 2 = 0 /\ xlo <= bv_unsigned a < xlo + xsz).
  { destruct H as [H|H]; [destruct (fetch_word_seg a w H) as (E & seg & IN & X & B1 & B2)| destruct (fetch_tail_seg a w H) as (E & seg & IN & X & B1 & B2)];
      destruct (XS seg IN X) as (EB & ES); split; [exact E| lia| exact E| lia]. }
  destruct R as (EA & RA).
  assert (OK : ok_at (bv_unsigned a) = true).
  { apply (scan2_sound g f xlo SC); [lia|]. rewrite Zminus_mod, EA, XE. reflexivity. }
  unfold ok_at in OK. rewrite Z_to_bv_bv_unsigned in OK. apply andb_true_iff in OK as [O1 O2].
  destruct H as [H|H]; [rewrite H in O1; exact O1| rewrite H in O2; exact O2].
Qed.

(* [comment removed for export] *)
Hypothesis fetch_safe : forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> word_frm_safe w = true.

Theorem step_fz : forall s s', RiscvSemantics.step segs s = MachineOk s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof.
  intros s s' H FZ. unfold RiscvSemantics.step, step_accesses in H.
  destruct (fetch_word segs (ms_pc s)) as [w|] eqn:F1.
  - destruct (decode_exec_accesses segs s w) as [r| | ] eqn:E; try discriminate. cbn [drop_access_report] in H. injection H as <-.
    exact (decode_exec_fz segs s w r FZ (fetch_safe _ _ (or_introl F1)) E).
  - rewrite fetch_word_ov_none, fetch_tail_any_eq in H.
    destruct (fetch_tail segs (ms_pc s)) as [w|] eqn:F2.
    + destruct (decode_exec_accesses segs s w) as [r| | ] eqn:E; try discriminate. cbn [drop_access_report] in H. injection H as <-.
      exact (decode_exec_fz segs s w r FZ (fetch_safe _ _ (or_intror F2)) E).
    + exfalso. unfold fetch_failure in H.
      (* #38 gave fetch_failure a LEADING vdso_text_at arm.  The two destructs below cannot
         absorb it: neither [negb _] nor [_ || _] unifies with [vdso_text_at _ _], so the first
         [discriminate] would meet a goal that is still an if-match.  Donor, THIS TREE, same
         class, already repaired: Mh_0036.v:3905-3910. *)
      destruct (vdso_text_at segs (ms_pc s)); [discriminate|].
      destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

Theorem msteps_fz : forall s s', msteps segs s s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof.
  intros s s' H. induction H as [ms| ms ms' ms'' P ST MS IH]; intros FZ; [exact FZ|].
  apply IH. exact (step_fz ms ms' ST FZ).
Qed.

(* [comment removed for export] *)
Corollary msteps_fz_mkst (fx fx' : FPState) R R' pc pc' M M' :
  msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs)) -> frm_zero (@fp_csr fx) -> frm_zero (@fp_csr fx').
Proof. intros MS FZ. exact (msteps_fz _ _ MS FZ). Qed.
End Generic.
End FRM.

End FrmKeep.
Module FrmKeepC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FPSteps.

From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_FrmKeepC () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsCeq_rewrite_relationI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes;EquivalenceEpointwise_equivalenceC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:Proper_mapc59OSSVerify5KrLib7Mh_00387CatExec=flat_map_app'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00387CatExec9skipn_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_00387CatExec>flat_map_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00387WallSim:u_len_wordC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv3Sem5is_x0C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics5Riscv3Sem9with_regsC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes6option00K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4rsetK47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes4bool00C4ELinuxProcessSemantics5Riscv3Sem7with_pcC4ELinuxProcessSemantics5Riscv3Sem9with_resvC4ELinuxProcessSemantics5Riscv3Sem:with_fregsc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC=fc_with_fregsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4fsetC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv3Sem7nan_boxc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC7fc_fsetC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem6fwriteI4ELinuxProcessSemantics5Riscv5Instr4ffmt00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics5Riscv3Sem6c_resvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3eqbK47Corelib4Init9Datatypes6option02c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC<fc_with_resvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem:inval_resvC4ELinuxProcessSemantics5Riscv3Sem6accrueC4ELinuxProcessSemantics5Riscv3Fpu;fflags_bitsC56Stdlib6ZArith6BinInt1Z3lorI4ELinuxProcessSemantics5Riscv3Fpu6fflags00c59OSSVerify5KrLib7Mh_00387FPSteps8frm_zeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387FPStepsDfp_fflags_bits_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387FPStepsBfp_frm_zero_accrueC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC9fc_accrueC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6bits_0C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z;shiftr_specK46Stdlib9micromega7EnvRing5PExpr03I47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool;andb_true_rC46Stdlib6ZArith:ZArith_dec8Z_lt_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z?bits_above_log2C47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic5False00c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC7fz_bitsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem9slice_getC45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics5Riscv3Sem9slice_setC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z4lnotC45stdpp9bitvector;definitions7bv_wrapC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool=orb_false_iffK46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions@bv_wrap_spec_lowC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_and_unsignedC56Stdlib6ZArith6BinInt1Z;shiftl_specC56Stdlib6ZArith6BinInt1Z8lor_specc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC8op_clearC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC>csr_frm_unsafeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01C45stdpp9bitvector;definitions5bv_orC45stdpp9bitvector;definitions6bv_notK4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff02c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC6eff_fzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387FPStepsDfp_frm_zero_slice0_5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC7fc_rsetC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or01c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC8fz_clearC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C4ELinuxProcessSemantics5Riscv3Sem8exec_csrC4ELinuxProcessSemantics5Riscv3Sem9with_fcsrI4ELinuxProcessSemantics5Riscv5Instr5csrop00I4ELinuxProcessSemantics5Riscv3Sem3eff00K4ELinuxProcessSemantics5Riscv5Instr5csrop01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5csrop02K4ELinuxProcessSemantics5Riscv5Instr5csrop03K4ELinuxProcessSemantics5Riscv5Instr5instr01C4ELinuxProcessSemantics5Riscv3Sem4c_pcC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions9bv_concatC4ELinuxProcessSemantics5Riscv7Prelude4sextK4ELinuxProcessSemantics5Riscv5Instr5instr02K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv5Instr5instr04C4ELinuxProcessSemantics5Riscv3Sem4rgetK4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv3Sem<branch_takenK4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics5Riscv3Sem3eff07K4ELinuxProcessSemantics5Riscv5Instr5instr07C45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics5Riscv3Sem3eff08C4ELinuxProcessSemantics5Riscv3Sem5low32c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC=fc_inval_resvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv5Instr5instr0;C4ELinuxProcessSemantics5Riscv3Sem5alu32K4ELinuxProcessSemantics5Riscv5Instr5instr0<K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr0>K4ELinuxProcessSemantics5Riscv5Instr5instr0?K4ELinuxProcessSemantics5Riscv5Instr5instr0BC4ELinuxProcessSemantics5Riscv3Sem7mul_divK4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv5Instr5instr0DC4ELinuxProcessSemantics5Riscv3Sem;amo_alignedK4ELinuxProcessSemantics5Riscv3Sem3eff06K4ELinuxProcessSemantics5Riscv5Instr5instr0EK4ELinuxProcessSemantics5Riscv5Instr5instr0FC4ELinuxProcessSemantics5Riscv3Sem7amo_valK4ELinuxProcessSemantics5Riscv5Instr5instr0GC4ELinuxProcessSemantics5Riscv3SemAcsr_write_illegalK4ELinuxProcessSemantics5Riscv3Sem3eff03c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC;exec_csr_fzC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0HK4ELinuxProcessSemantics5Riscv5Instr5instr0IK4ELinuxProcessSemantics5Riscv5Instr5instr0JC4ELinuxProcessSemantics5Riscv3Sem4fgetK4ELinuxProcessSemantics5Riscv5Instr5instr0KC4ELinuxProcessSemantics5Riscv3Sem:resolve_rmC4ELinuxProcessSemantics5Riscv3Sem5freadC4ELinuxProcessSemantics5Riscv3Sem9fp_formatC4ELinuxProcessSemantics5Riscv3Fpu6fp_negC4ELinuxProcessSemantics5Riscv3Fpu6fp_fmac69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC9fz_accrueC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC9fc_fwriteC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0LC4ELinuxProcessSemantics5Riscv3Fpu6fp_addC4ELinuxProcessSemantics5Riscv3Fpu6fp_subC4ELinuxProcessSemantics5Riscv3Fpu6fp_mulC4ELinuxProcessSemantics5Riscv3Fpu6fp_divK4ELinuxProcessSemantics5Riscv5Instr5instr0MC4ELinuxProcessSemantics5Riscv3Fpu7fp_sqrtK4ELinuxProcessSemantics5Riscv5Instr5instr0NC4ELinuxProcessSemantics5Riscv3Sem7unbox_sC4ELinuxProcessSemantics5Riscv3Sem8sgnj_valK4ELinuxProcessSemantics5Riscv5Instr5instr0OC4ELinuxProcessSemantics5Riscv3Fpu9fp_minmaxK4ELinuxProcessSemantics5Riscv5Instr5instr0PC4ELinuxProcessSemantics5Riscv3Fpu5fp_eqC4ELinuxProcessSemantics5Riscv3Fpu5fp_ltC4ELinuxProcessSemantics5Riscv3Fpu5fp_leK4ELinuxProcessSemantics5Riscv5Instr5instr0QC4ELinuxProcessSemantics5Riscv3Fpu:fp_convertC4ELinuxProcessSemantics5Riscv3Fpu9fp_of_intC4ELinuxProcessSemantics5Riscv3Fpu9fp_to_intK4ELinuxProcessSemantics5Riscv5Instr5instr0RK4ELinuxProcessSemantics5Riscv5Instr5instr0SC4ELinuxProcessSemantics5Riscv3Fpu8fp_classc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC>instr_frm_safeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4execI4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w1I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00I4ELinuxProcessSemantics5Riscv5Instr5msize00K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv5Instr5aluop00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0@K4ELinuxProcessSemantics5Riscv5Instr5instr0AI4ELinuxProcessSemantics5Riscv5Instr5mulop00I4ELinuxProcessSemantics5Riscv5Instr6awidth00K4ELinuxProcessSemantics5Riscv5Instr6awidth01K4ELinuxProcessSemantics5Riscv5Instr6awidth02C4ELinuxProcessSemantics5Riscv3Sem2w0I4ELinuxProcessSemantics5Riscv5Instr5amoop00K4ELinuxProcessSemantics5Riscv5Instr4ffmt01K4ELinuxProcessSemantics5Riscv5Instr4ffmt02I4ELinuxProcessSemantics5Riscv5Instr5fmaop00I4ELinuxProcessSemantics5Riscv3Fpu5rmode00I4ELinuxProcessSemantics5Riscv5Instr6fariop00I4ELinuxProcessSemantics5Riscv5Instr6fsgnop00I4ELinuxProcessSemantics5Riscv5Instr9fminmaxop00I4ELinuxProcessSemantics5Riscv5Instr6fcmpop00I4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty00I4ELinuxProcessSemantics5Riscv5Instr6fmvdir00K4ELinuxProcessSemantics5Riscv5Instr6fmvdir01K4ELinuxProcessSemantics5Riscv5Instr6fmvdir02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics5Riscv3Sem3eff04K4ELinuxProcessSemantics5Riscv3Sem3eff05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;width_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics5Riscv3Sem7eff_indK47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib7Numbers7BinNums1N00c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC=word_frm_safeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC7exec_fzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC9interp_fzC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z3lebC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType>seg_executableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC56Stdlib6NArith6BinNat1N6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsAseg_ov_read_bytesc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC?find_segment_InC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<code_read_ovC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le4c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMCAcode_read_ov_noneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_halfC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_half_ovC4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le2C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_half_anyC4ELinuxProcessSemantics5Riscv7Prelude4bitsc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMCAfetch_half_any_eqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_tailC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBsegment_read_bytesI47Corelib4Init5Logic2ex00c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMCBfind_segment_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9code_readc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC=code_read_segC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC5scan1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC5ok_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init9Datatypes3nat02C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6eq_decC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega:ZMicromega;ZArithProof01c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC5scan2C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC;scan1_soundC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC>fetch_word_segC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC>fetch_tail_segC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Zminus_modc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC;scan2_soundC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failurec69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC>decode_exec_fzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMCBfetch_word_ov_noneC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMCAfetch_tail_any_eqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@fetch_byte_trapsI59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC7step_fzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:msteps_indC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC9msteps_fzC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00387FrmKeep3FRM>instr_frm_safeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00387FrmKeep3FRM:csr_writesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00387FrmKeep3FRM>csr_frm_unsafeC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffc69OSSVerify5KrLib7Mh_00388FrmKeepC4FRMC:csr_writesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00387FrmKeep3FRM=word_frm_safeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FRMC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition csr_frm_unsafe (writes : bool) (csr : bv 12) : bool :=
  writes && ((bv_unsigned csr =? 2) || (bv_unsigned csr =? 3)).
Definition csr_writes (op : csrop) (nz : bool) : bool := match op with CSR_RW => true | _ => nz end.
(* [comment removed for export] *)
Definition op_clear (op : csrop) : bool := match op with CSR_RC => true | _ => false end.
Definition instr_frm_safe (i : instr) : bool :=
  match i with
  | Csr op rd rs1 csr => op_clear op || negb (csr_frm_unsafe (csr_writes op (negb (is_x0 rs1))) csr)
  | CsrI op rd uimm csr => op_clear op || negb (csr_frm_unsafe (csr_writes op (negb (Z.eqb (bv_unsigned uimm) 0))) csr)
  | _ => true
  end.
Definition word_frm_safe (w : bv 32) : bool :=
  match decode_any w with Some (i, _) => instr_frm_safe i | None => true end.

(* [comment removed for export] *)
Fixpoint eff_fz (e : eff) : Prop :=
  match e with
  | EDone c => frm_zero (c_fcsr c)
  | ELoad n a k => forall v, eff_fz (k v)
  | EStore n a v k => eff_fz k
  | _ => True
  end.

(* [comment removed for export] *)
Lemma fc_rset r v c : c_fcsr (rset r v c) = c_fcsr c.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "p'0h01ci001ch11rh21vh31bi011bh46c_fcsri026c_fcsrh57c_fregsi037c_fregsh64c_pci044c_pch76c_regsi056c_regsh86c_resvi066c_resvp;1p;4p;2p;3p;5p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p4p710RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p4p7210R=P9p8P=P5p8P=P0p8P=P@p8p100EEp4p710R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp4p710REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp4p7210RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8g00H`R@p4p7210RBP7p8PBP:p8PBP;p8PBP5p8PBp100ILp4p710p8PBp100Iip4p710p8PBp100K0p4p710p8p100L:p4p710P5p8p100LUp4p70RBP1p8PBP2p8PBP7p8PBP:p8PBP;p8PBP4p8PBP3p8PBP<p8PBP5p8PBP6p8P>P5p8p100MKp4p710R>p100NJp4p710p8P>P8p8PEP7p8PEP5p8g00OBj11Tg00Ogj1=Tg00PLj13Tg00Pjj14Tg00QMj1<Tg00R5j4:Tg00Rej26Tg00SQj10Tg00T:j32Tg00TTj25TP@j27Tg00Tnj18Tg00UPj59Tg00V9j3;Tg00V`#1R@#=#3R5#4RE%1@#1#1#1R@#1#3#4R7g00WER8f2R>#<g00WnR6P6%3@#4R@P6P8f0R6P>P5P7f4RBf3R<C:R3/6>n0100000020000#0%0>32P6f1R4#0,5@P81636#0%06R352@P41757R5%87PBP<P>P4P6D9#0,5@W8X4@X67X55W7PBP<P>P4P6O5n01100000150105103104102106n0110100020000b3A;>46#0=2@3eX08X27X1EP>P4P6O3W0W2W1o"). Qed.
Lemma fc_with_pc v c : c_fcsr (with_pc v c) = c_fcsr c.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "p'0h01ci001ch11vh26c_fcsri016c_fcsrh37c_fregsi027c_fregsh44c_pci034c_pch56c_regsi046c_regsh66c_resvi056c_resvp;1p;2p;3p;5p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p4p710RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p4p7210R=P9p8P=P5p8P=P0p8P=P@p8p100EEp4p710R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp4p710REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp4p7210RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8g00H`R@p4p7210RBP7p8PBP:p8PBP;p8PBP5p8PBp100ILp4p710p8PBp100Iip4p710p8PBp100K0p4p710p8p100L:p4p710P5p8p100LUp4p70RBP1p8PBP2p8PBP7p8PBP:p8PBP;p8PBP4p8PBP3p8PBP<p8PBP5p8PBP6p8P>P5p8p100MKp4p710R>p100NJp4p710p8P>P8p8PEP7p8PEP5p8g00OBj10Tg00PLj11Tg00Pjj13Tg00XNj24Tg00SQj12Tg00T:j3:Tg00Ogj19TP@j25Tg00Tnj16Tg00UPj57Tg00TTj28Tg00V`#0R@#0#0#0#0R5#0#1#3REg00WER7P7%15#3R5f2R8f0R>'4#2%2>3:P>%9@#1/5ER@%6Ef4R6f3RBP8f1R<P>D7#2,85W6X25X4EX3@W5P6PBP8P<P>O5n01100000150104102103101105X07X1EP<P>O2W0W1o"). Qed.
Lemma fc_with_resv v c : c_fcsr (with_resv v c) = c_fcsr c.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "p'0h01ci001ch11vh26c_fcsri016c_fcsrh37c_fregsi027c_fregsh44c_pci034c_pch56c_regsi046c_regsh66c_resvi056c_resvp;1p;2p;3p;5p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p4p710RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p4p7210R=P9p8P=P5p8P=P0p8P=P@p8p100EEp4p710R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp4p710REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp4p7210RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8g00H`R@p4p7210RBP7p8PBP:p8PBP;p8PBP5p8PBp100ILp4p710p8PBp100Iip4p710p8PBp100K0p4p710p8p100L:p4p710P5p8p100LUp4p70RBP1p8PBP2p8PBP7p8PBP:p8PBP;p8PBP4p8PBP3p8PBP<p8PBP5p8PBP6p8P>P5p8p100MKp4p710R>p100NJp4p710p8P>P8p8PEP7p8PEP5p8g00OBj10Tg00PLj12Tg00Pjj13Tg00Tnj14Tg00Y8j2:Tg00SQj11Tg00T:j39Tg00Ogj15TP@j26Tg00UPj57Tg00TTj28Tg00V`#0R@#0#0#0#0R5#0#2#3RE#4R7g00WER8P8%25#3R5f2R>f0R6':#1%1639P6%5@#2/6ER@f4RBf3R<P>f1R3P6D7#1,85X67X25X4EX3@W5PBP<P>P3P6O5n01100000150104102103101105X08X17P3P6O2W0W1o"). Qed.
Lemma fc_with_regs f c : c_fcsr (with_regs f c) = c_fcsr c.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "p'0h01ci001ch11fh26c_fcsri016c_fcsrh37c_fregsi027c_fregsh44c_pci034c_pch56c_regsi046c_regsh66c_resvi056c_resvh71xp;1p;2p;3p;5p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p4p710RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p4p7210R=P9p8P=P5p8P=P0p8P=P@p8p100EEp4p710R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp4p710REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp4p7210RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8g00H`R@p4p7210RBP7p8PBP:p8PBP;p8PBP5p8PBp100ILp4p710p8PBp100Iip4p710p8PBp100K0p4p710p8p100L:p4p710P5p8p100LUp4p70RBP1p8PBP2p8PBP7p8PBP:p8PBP;p8PBP4p8PBP3p8PBP<p8PBP5p8PBP6p8P>P5p8p100MKp4p710R>p100NJp4p710p8P>P8p8PEP7p8PEP5p8g00OBj10Tg00Ogj1:Tg00PLj11Tg00Pjj13TP@j29Tg00Rej28Tg00SQj12Tg00T:j35Tg00Tnj16Tg00UPj57Tg00TTj24Tg00V`#0R@#:#1%0@#0#0#0R@#0#1#3R5'9REPE]7R7g00WER8P8%1@#3R@f2R>f0R6'8#2%2635P6%65f4RBf3R<P>f1R3P6D7#2,4@W6X2@X45X3EX5EPBP<P>P3P6O5n01100000150104102103101105X08X17P3P6O2W0W1o"). Qed.
Lemma fc_with_fregs f c : c_fcsr (with_fregs f c) = c_fcsr c.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "p'0h01ci001ch11fh26c_fcsri016c_fcsrh37c_fregsi027c_fregsh44c_pci034c_pch56c_regsi046c_regsh66c_resvi056c_resvh71xp;1p;2p;3p;5p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p4p710RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p4p7210R=P9p8P=P5p8P=P0p8P=P@p8p100EEp4p710R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp4p710REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp4p7210RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8g00H`R@p4p7210RBP7p8PBP:p8PBP;p8PBP5p8PBp100ILp4p710p8PBp100Iip4p710p8PBp100K0p4p710p8p100L:p4p710P5p8p100LUp4p70RBP1p8PBP2p8PBP7p8PBP:p8PBP;p8PBP4p8PBP3p8PBP<p8PBP5p8PBP6p8P>P5p8p100MKp4p710R>p100NJp4p710p8P>P8p8PEP7p8PEP5p8g00OBj10Tg00Ogj1:Tg00PLj11Tg00Pjj13TP@j29Tg00Ydj28Tg00SQj12Tg00T:j35Tg00Tnj16Tg00UPj57Tg00TTj24Tg00V`#0R@#:#1%0@#0#0#0R@#0#1#3R5'9REPE]7R7g00WER8P8%1@#3R@f2R>f0R6'8#2%2635P6%65f4RBf3R<P>f1R3P6D7#2,4@W6X2@X45X3EX5EPBP<P>P3P6O5n01100000150104102103101105X08X17P3P6O2W0W1o"). Qed.
Lemma fc_fset r v c : c_fcsr (fset r v c) = c_fcsr c.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "h01ch11rh21vp;1p;4p;2p;3p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p4p710RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p4p7210R=P9p8P=P5p8P=P0p8P=P@p8p100EEp4p710R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp4p710REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp4p7210RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8p100H`p4p7210R@P7p8P@P:p8P@P;p8P@P5p8P@p100ILp4p710p8P@p100Iip4p710p8P@p100K0p4p710p8p100L:p4p710P5p8p100LUp4p70R@P1p8P@P2p8P@P7p8P@P:p8P@P;p8P@P4p8P@P3p8P@P<p8P@P5p8P@P6p8P>P5p8p100MKp4p710R>p100NJp4p710p8P>P8p8PEP7p8PEP5p8g00OBj10Tg00Ogj18Tg00PLj12Tg00Pjj11Tg00R5j47Tg00ZQj26Tg00[Yj35Tg00SQj13Tg00T:j34Tg00V`#0R5#8#2RE#1R7%05#0#0#0R5#0#2#1R8g00WER>PEP8f2REf1R6C7f0R@'6%25#1A5E6@#3%3@34eX0>X28X17PEP6P@O3W0W2W1o"). Qed.
Lemma fc_fwrite fmt r v c : c_fcsr (fwrite fmt r v c) = c_fcsr c.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "p'0h01ch13fmti003fmth21rh31vi011fp;1p;2p;3p;4p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p4p710RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p4p7210R=P9p8P=P5p8P=P0p8P=P@p8p100EEp4p710R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp4p710REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp4p7210RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8p100H`p4p7210R@P7p8P@P:p8P@P;p8P@P5p8P@p100ILp4p710p8P@p100Iip4p710p8P@p100K0p4p710p8p100L:p4p710P5p8p100LUp4p70R@P1p8P@P2p8P@P7p8P@P:p8P@P;p8P@P4p8P@P3p8P@P<p8P@P5p8P@P6p8P>P5p8p100MKp4p710R>p100NJp4p710p8P>P8p8PEP7p8PEP5p8g00OBj10Tg00Ogj1:Tg00PLj13Tg00Pjj14Tg00\@j22Tg00\fj18Tg00[Yj37Tg00SQj11Tg00T:j35Tg00]Pj36Tg00^Rj49Tg00_;R5g00V`#0RE#:#3#4R7g00_fR8g00WER>P5%0E#0#0#0RE#3R6#4R@P5P>f0R<f3R3f2R4,26#8f1R;37%0E#3RE/24=73;n0110000020000#1%1;35P3126;#8=64<12E;=64<n0110100020000P3P4P;P<C9#1%1<55@eX0>X38X27X15P3P4P;P<O4W0W3W2W1o"). Qed.
Lemma fc_inval_resv a c : c_fcsr (inval_resv a c) = c_fcsr c.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "p'0h01ah11ch21bi001bh31oi011oh42r0i021ri031xp;1p;2p;3p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p4p710RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p4p7210R=P9p8P=P5p8P=P0p8P=P@p8p100EEp4p710R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp4p710REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp4p7210RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8p100H`p4p7210R@P7p8P@P:p8P@P;p8P@P5p8P@p100ILp4p710p8P@p100Iip4p710p8P@p100K0p4p710p8p100L:p4p710P5p8p100LUp4p70R@P1p8P@P2p8P@P7p8P@P:p8P@P;p8P@P4p8P@P3p8P@P<p8P@P5p8P@P6p8P>P5p8p100MKp4p710R>p100NJp4p710p8P>P8p8PEP7p8PEP5p8g00OBj11Tg00PLj17Tg00Pjj13Tg00`Dj18Tg00TnR5j1=Tg00`mj24Tg00aWj2;Tg00b4j1:Tg00Y8j25Tg00SQj10Tg00T:j32Tg00bVj29Tg00TTj26Tg00c]j2<Tg00V`#1#1#1#1#1RE#1#7R7#3R8g00WER>f0R6#8%=8P5P8%7E#3REP5P8P>P6g00WnR5P>1476f4R@,47';R7%:8R<f3R3'5P3n0100000020000f2R3n10110300021010200#0%0332P6P7P5P5P5P>P6f5R5,5<P5n0100000020000#0%0552EP619<@%0@,6En0110000020000b2X48P6O1f1R@#0,6En10110100021010000b31<@6#0%0652EeX1>X08P@P6O2W1W0o"). Qed.
Lemma fc_accrue fl c : c_fcsr (accrue fl c) = Z_to_bv 32 (Z.lor (bv_unsigned (c_fcsr c)) (fflags_bits fl)).
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "p'0h01ci001ch12flh26c_fcsri016c_fcsrh37c_fregsi027c_fregsh44c_pci034c_pch56c_regsi046c_regsh66c_resvi056c_resvp;1p;2p;3p;5p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p4p710RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p4p7210R=P9p8P=P5p8P=P0p8P=P@p8p100EEp4p710R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp4p710REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp4p7210RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8g00H`R@p4p7210RBP7p8PBP:p8PBP;p8PBP5p8PBp100ILp4p710p8PBp100Iip4p710p8PBp100K0p4p710p8p100L:p4p710P5p8p100LUp4p70RBP1p8PBP2p8PBP7p8PBP:p8PBP;p8PBP4p8PBP3p8PBP<p8PBP5p8PBP6p8P>P5p8p100MKp4p710R>p100NJp4p710p8P>P8p8PEP7p8PEP5p8g00OBj10Tg00PLj11Tg00Pjj13Tg00dJj2;Tg00SQj12Tg00`mj27Tg00e3j16Tg00eaj24Tg00\@j25Tg00T:j3<Tg00Ogj1:TP@j28Tg00Tnj19Tg00UPj5>Tg00TTj2=Tg00f>R@g00WER5P5g00V`#0RE#0#0#0#0R7#1R8#3R>f2R6f0RB';#2%2B,78%66'4,583<PB%:E#1%07#1#3R7'8RE%97f4R<f3R3P6f1R4PBD>#2,78f;#6'4,58,=>W6X2>X47X3EW5P<P3P6P4PBO5n01100000150104102103101105X05X1@P4PBO2W0W1o"). Qed.
Lemma fz_accrue fl c : frm_zero (c_fcsr c) -> frm_zero (c_fcsr (accrue fl c)).
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "h01ch12flh21Hh31bp;1p;2p;4p;6p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0p1004Np4p710R8p8P0p1004ep4p710R9p8P0p1005Ep4p710R0p8p1005bp4p70R:P8p8P:P1p8P:P2p8P:p1006Rp4p710R8p8P:p1006np4p710R;p8P:p1007Lp4p7210R<p8P:P4p8P:P3p4p710R3p8P:p1007ip4p710R=p8P:p1008Yp4p710p8P:P6p8P:P7p8P:p1009:p4p710p8p1009Wp4p710R:P8p8P:P6p8p100:4p4p70R>P1p8P>P2p8P>p100:bp4p7210p8P>P8p8P>p100;>p4p710p8P>p100<4p4p7210p8P>P:p8P>P;p8P>p100<cp4p710p8P>P<p8P>p100=^p4p710p8P>p100>Xp4p710p8P>P4p8P>P3p8P>p100?Tp4p710p8P>P=p8P>P6p8P>p100@Np4p7210p8P>P7p8P>P0p8P>p100ABp4p710p8P>p100BHp4p7210R?p8P>p100BeR@p4p7210RAp8P>p100CBp4p7210p8p100CaR>p4p710RBp100Dcp4p710RCp8PBP0p8PBP@p4p710R@p8P>p4p7210R>P:p8P>P6p8P>P0p8P>PAp8p100EEp4p710R:p100FCp4p710RDp8P:p100F_p4p710REp8P:PCp8P:P9p8p100G>RCp4p710RFP1p8PFP2p8PFPDp8PFPEp8PFP4p8PFP3p8PFP6p8PFP7p8PFPBp8PFP:p8PFP9p8PFP0p8PFP@p8PFp100HAp4p710RFp8PCp4p7210RCP1p8PCP2p8PCP4p8PCP3p8PCP=p8PCP7p8PCP>p8PCP0p8PCPAp8p100H`p4p7210RAP8p8PAP;p8PAP<p8PAP6p8PAp100ILp4p710p8PAp100Iip4p710p8PAp100K0p4p710p8p100L:p4p710P6p8p100LUp4p70RAP1p8PAP2p8PAP8p8PAP;p8PAP<p8PAP4p8PAP3p8PAP=p8PAP6p8PAP7p8P?P6p8p100MKp4p710R?p100NJp4p710p8P?P9p8PFP8p8PFP6p8g00SQj11Tg00fij12Tg00OBj10Tg00PLj13Tg00Pjj1=Tg00`mj2;Tg00e3j1:Tg00eaj24Tg00\@j25Tg00gfj16Tg00hoj47Tg00dJj28Tg00j6j29TP5j6<Tg00f>R5g00WER6f0RF#1#2g00V`#0#0#0#0#0#3R8#=R9f1R?#1R7,;8f2RA#:R='4,58%2FX39P7P=%6APFC718A?#119A?E<W2X06X15P?PFO2W0W1o"). Qed.

Ltac fz_core FZ :=
  repeat first [ exact FZ
               | rewrite fc_rset | rewrite fc_with_pc | rewrite fc_with_resv | rewrite fc_with_regs | rewrite fc_fset
               | rewrite fc_fwrite | rewrite fc_inval_resv | apply fz_accrue ].

Ltac fz_tree FZ :=
  repeat first [ lazymatch goal with
                 | |- eff_fz (match ?x with _ => _ end) => destruct x
                 | |- eff_fz ((match ?x with _ => _ end) _) => destruct x
                 | |- eff_fz (EDone _) => cbn [eff_fz]
                 | |- eff_fz (ELoad _ _ _) => cbn [eff_fz]; intros ?
                 | |- eff_fz (EStore _ _ _ _) => cbn [eff_fz]
                 | |- eff_fz (exec_csr _ _ _ _ _ _) => fail
                 | |- eff_fz _ => exact I
                 | |- frm_zero (c_fcsr (match ?x with _ => _ end)) => destruct x
                 | |- frm_zero _ => progress (fz_core FZ)
                 end ].

(* [comment removed for export] *)
Lemma fz_bits (u : Z) : Z.land (Z.shiftr u 5) 7 = 0 <-> (forall i, 5 <= i < 8 -> Z.testbit u i = false).
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "p'0h04__x1h12H0h27__arithh34__ffh48__varmaph55__with61bh71Th81ih91zh:1Hh;4__p1h<1uh=1Bh>2Geh?2Hih@2HnhA2LthB1ni001nhC1si011si021lp;1p;2p;6p;3p;4p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0p1004Np4p710R8p8P0p1004ep4p710R9p8P0p1005Ep4p710R0p8p1005bp4p70R:P8p8P:P1p8P:P2p8P:g006RR8p4p710R;p8P:p1006np4p710R<p8P:p1007Lp4p7210R=p8P:P4p8P:P3p4p710R3p8P:p1007ip4p710R>p8P:p1008Yp4p710p8P:P6p8P:P7p8P:p1009:p4p710p8p1009Wp4p710R:P;p8P:P6p8p100:4p4p70R?P1p8P?P2p8P?p100:bp4p7210p8P?P;p8P?p100;>p4p710p8P?p100<4p4p7210p8P?P:p8P?P<p8P?p100<cp4p710p8P?P=p8P?p100=^p4p710p8P?p100>Xp4p710p8P?P4p8P?P3p8P?p100?Tp4p710p8P?P>p8P?P6p8P?p100@Np4p7210p8P?P7p8P?P0p8P?p100ABp4p710p8P?p100BHp4p7210R@p8P?p100BeRAp4p7210RBp8P?p100CBp4p7210p8p100CaR?p4p710RCp100Dcp4p710RDp8PCP0p8PCPAp4p710RAp8P?p4p7210R?P:p8P?P6p8P?P0p8P?PBp8p100EEp4p710R:p100FCp4p710REp8P:p100F_p4p710RFp8P:PDp8P:P9p8p100G>RDp4p710RGP1p8PGP2p8PGPEp8PGPFp8PGP4p8PGP3p8PGP6p8PGP7p8PGPCp8PGP:p8PGP9p8PGP0p8PGPAp8PGp100HAp4p710RGp8PDp4p7210RDP1p8PDP2p8PDP4p8PDP3p8PDP>p8PDP7p8PDP?p8PDP0p8PDPBp8p100H`p4p7210RBP;p8PBP<p8PBP=p8PBP6p8PBp100ILp4p710p8PBp100Iip4p710p8PBp100K0p4p710p8p100L:p4p710P6p8p100LUp4p70RBP1p8PBP2p8PBP;p8PBP<p8PBP=p8PBP4p8PBP3p8PBP>p8PBP6p8PBP7p8P@P6p8p100MKp4p710R@p100NJp4p710p8P@P9p8PGP;p8PGP6p8g00OBj1LTg00Ogj1MTg00k:j1<Tg00kXj2@Tg00l8j2DTg00lVj2;Tg00m2j27Tg00mNj2ITg00mij20Tg00nJj23Tg00ngj1NTP5j66Tg00oGj2FTg00oej3QTP8j6BTg010Hj24Tg010ej1bTg011Ej1`Tg011ej2_Tg012Cj1^Tg012aj1]Tg013Lj2\Tg013oj6[Tg00b4j1ZTg014Sj2PTg0156j3YTg015Yj2XTg00TTj2OTg016;j2WTg016gj3VTg017Fj4UTg0188j4TTg018]j3STg019@R8j2>Tg019Zj1oTg00T:j39Tg01:9j2nTg01:]j1KTg01;6R5j2mTg01;Vj1lTg01<4j6kTg01<Xj4fTg01=Aj4cTg01=]j1dTg01>=j3eTg01>`j4aTg01?;j4JTg01?fj7gTg01@Jj7hTg01@nj8iTg01ARj7jTg00_fR6f0RGg01B6R;39p==g00WnR9g01BTR@79Gp=8f1R7/FG=99@p=51P6Gp=?P6P7g01C4PGCJp=AP7g01C[RBg01D:R>P>g01DZR3PGg01E:Fgp=2f2R4PBP>P>P3P7PGFhp=Hf3R=PBP>P>P3P4P7PGGip=:g01EZR<999Gp=CP6P7g01F:PGCJp=GA967Gp=1P6P7g01FaPGCJp=EP4PBP>P>P3P7PGFjp=Rg00V`R2#LR1#M#<RD,@G%M2R0#M#<R?'D#=RA1;DGR:%L1#L#<RC,7G'IRF10=7#8[^86[1047#8\F^86RE1@7D/D?RH#=[P6P;134DRI,0G#8X96137DRJ#N1@=DRK/D?RLP4E610LJ#8P9f4RM/@DRN/D?RO/0I%8GX69RPPG10NI10?I'FRQAQN?IEB%8QP9f5RQ/@D13=DRN'013MDRI,0?,5GX69PG14ND,0QRRPQPDPNp-0RSg01GHRT#bRU%`TRT1_67RV%^6RW%]6RX%?DRY1\62RZ'A,2XR[PXPBP>P>P3P=E[5HX%Z>R\1P6;R]AY6ZYR^'A,2XC:1XX3R_PGP41O9<R`1WG4#CdAV6;7CURab3b4b5X06W;1I:71;;J[^06^;SPG17MCPMP=O3b2CTEB10?N,5RPUPTPVPWAS6^Y,GZ,2XP_Pab3b4b5X0613GD/4D,1G^06PGPQO1b214ID,1MP613QDRI/4Df8RR/0Gf6RN/3DRS,0?R:'5X96P7PQPGE6f7Rb/0Q10?I'5PUPTPVPWPX%?CRI,EZ,2X9HX[P\1G^],2X%<2R2#?,G^,2X%<1R1#?R[,G^,2X5RX5RXC:P_Pab3b4b5X06%=J11J211J1'>'>\F^06PGPbPNO2b2%=S11S211S1'>'>P813bDRS#=11S211S1'>13RDRJ,0?#CPG%=JP6P;10?G#CX96R^P`f9Rc/3DRdPGE6W1PGO111J211J1'>P811d211d1f:Rd/3DR8,0?#CPG1182P6P2P^P`f;/3DR2PGE6W1PGO11181P6P1P^P`P2PGE6W1PGO1n200100000021000010000W1PGO1n200100000021000010000b1%C:P910?S10dRRd/5GX69P7P<PGEB10cb/5<P91Fd<PPPGPd%odEB%8dPGb7b7b=b7b1b7b7b7X?FX86X:A1;;GRAP9P@10O4=99GX69P910K7RO10?7'FPPP9147D,0=10?4,5GX69%<0R0,n71770RP%KP'mP51740R5%K514=D,0Q10?='5PG17=0R5P9P@10?QRP,5GX691O9@14MDRF,0NPQPFPUPTPVPWPX%?0,EZ,2XRFP\PX1A]Z,2XRdP\AS6ZYR<,AY,2X1E<I,2X5HXC:C:P_Pab3b4b5X0617G0R01;;7R<144DRI,;D17IC'I[[^06PGPQP7PMO3b2O2E6WAPGO1%K5P910?MR5P@P?PMPUPT%l6PW%??,A],2XP_Pab3b4b51;;?PGb2PUPTPVPWPXPXPBP>P>P3PFEkP\1E[Z,2XC:P_Pab3b4b5X06g01H4\01717[^06PGPQP7O2b2CfCcA99@5P9P@14ND,0R/5GX6914QD,0b#dPPPGEBb1W>PGO1n200110100021110211100bCPOP=PDP7PUPTPVPWPXPdP\PdC:P_Pab3b4b5X06P<\A^06PGP4P7O2b2CTE610L7AQK?7E610;7%N7E6W@XB69eH;X:ECaX<6PGO1X<6o"). Qed.
(* [comment removed for export] *)
Lemma fz_clear (f : bv 32) (lo len : Z) (y : word) :
  ((lo = 5 /\ len = 3) \/ (lo = 0 /\ len = 8)) -> frm_zero f -> frm_zero (slice_set f lo len (bv_and (slice_get f lo len) y)).
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "h01Hh14__x1h22Hih37__arithh44__ffh58__varmaph65__with71ih84__x2h91bh:2loh;3lenh<1zh=2H0h>4__p1h?2b1h@2b2hA1fhB1uhC1yhD1BhE1ChF2FZhG2I3hH2LOp%0p&0p;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0p1004Np4p710R8p8P0p1004ep4p710R9p8P0p1005Ep4p710R0p8p1005bp4p70R:P8p8P:P1p8P:P2p8P:g006RR8p4p710R;p8P:p1006np4p710R<p8P:p1007Lp4p7210R=p8P:P4p8P:P3p4p710R3p8P:p1007ip4p710R>p8P:p1008Yp4p710p8P:P6p8P:P7p8P:p1009:p4p710p8p1009Wp4p710R:P;p8P:P6p8p100:4p4p70R?P1p8P?P2p8P?p100:bp4p7210p8P?P;p8P?p100;>p4p710p8P?p100<4p4p7210p8P?P:p8P?P<p8P?p100<cp4p710p8P?P=p8P?p100=^p4p710p8P?p100>Xp4p710p8P?P4p8P?P3p8P?p100?Tp4p710p8P?P>p8P?P6p8P?p100@Np4p7210p8P?P7p8P?P0p8P?p100ABp4p710p8P?p100BHp4p7210R@p8P?p100BeRAp4p7210RBp8P?p100CBp4p7210p8p100CaR?p4p710RCp100Dcp4p710RDp8PCP0p8PCPAp4p710RAp8P?p4p7210R?P:p8P?P6p8P?P0p8P?PBp8p100EEp4p710R:p100FCp4p710REp8P:p100F_p4p710RFp8P:PDp8P:P9p8p100G>RDp4p710RGP1p8PGP2p8PGPEp8PGPFp8PGP4p8PGP3p8PGP6p8PGP7p8PGPCp8PGP:p8PGP9p8PGP0p8PGPAp8PGp100HAp4p710RGp8PDp4p7210RDP1p8PDP2p8PDP4p8PDP3p8PDP>p8PDP7p8PDP?p8PDP0p8PDPBp8p100H`p4p7210RBP;p8PBP<p8PBP=p8PBP6p8PBp100ILp4p710p8PBp100Iip4p710p8PBp100K0p4p710p8p100L:p4p710P6p8p100LUp4p70RBP1p8PBP2p8PBP;p8PBP<p8PBP=p8PBP4p8PBP3p8PBP>p8PBP6p8PBP7p8P@P6p8p100MKp4p710R@p100NJp4p710p8P@P9p8PGP;p8PGP6p8g00OBj1ETg00PLj1jTg00Pjj1eTg00Ogj1WTg00k:j1BTg00mNR6j2:Tg019@RGj2FTg00fij1iTg00kXj2DTg00l8j29Tg00lVj2LTg00mij20Tg01HQj1hTg01ISj3QTg01J?j3RTg01Jdj4[Tg00`mj23Tg01KPk400Tg010ej1zTg011Ej1vTg011ej2aTg012Cj1sTg012aj1qTg013Lj2gTg00b4j1mTg015Yj2lTg00TTj2VTg016;j2kTg00T:j3KTg016gk307Tg017Fk406Tg01Kkj1@Tg01LIj27Tg01Lij1?Tg00eak205Tg01MGj2^Tg01Mmj2UTg01NJk204Tg00oGj25TP5j6Pj7nTg01=]k103TP8j6\Tg00oej3TTg00nJj2;Tg00m2j2OTg014Sj2fTg0156j3ZTg010Hj2YTg01;Vj1yTg01Nkj4xTg018]j3wTg0188j4uTg01OIj1bTg01Ogj4`Tg00\@j2cTg01PVj2dTg01QEj3tTg013oj6rTg01R3j4{Tg01=Aj4|Tg01>`j4}Tg01RXj3~Tg01?;j4XTg01?fj7pTg01@Jk701Tg01ARk702Tg01@nj8oTg00_fR8f1R5f0R;3Kp=1g01B6R99K8;p=<f2R@1O5;':p=4g00WnR7g01BTRB7K;p=21f8;p=HP8P5g01C4P;CXp=NP5g01C[R>g01D:R3P3g01DZR4P;g01E:Fpp=6P8P5g01FaP;CXp=MP@P>P3P3P4P5P;K01p=GP8P5g01F:P;CXp=SP@P>P3P3P4P5P;K02p=_f3R=P>P3P3P4P@P5P;Gop=AAK7B;p=]105;9K7Bp==1V7;p=IP8f5R<f4R2P=P@P5P;Fnp=JP8P2P=P@P5P;EPp=CP7P2P=P@P5P;EPp=>1L9;p=8g00V`R1#ERD#E#ER0#E#ER?#jRA#eS00%E?S01#jR:#eS02Q00Q02%WD#BRC,1@RF%W1RE#BRH,15':%<@%B0R0,15':'F%i2P61D;C%WE#BRI'9#<1LC;S03?4;0RJ10=5#2[^78RK[10@5#2\J^781D5C/9I#<[RL1D@C/9I#<\K%h;P;n2001000000120000000XB8PL^B8P;f6RLP<P2AQL<2=R:=C[,3Af8RK,3ARM/DC/9I#<f;RN,3ARO/05#2\J^78[f:RP,3ARQ/05#2\J^78RRf9RS,3A/DC/9I#<[%hMP=H00PRg01GHRR#zRM%vRRR1a85RT%s8RU%q8RV%HCRW1g81R1'N,6VS04%H0,M1,6V5GVRX%m3RY1S1W,6V%EE#BRE#H,S1,6V%HI,S1,6V5_V5_VCA1lV4RZP;P@g01EZR[,V71k;@=K7[dB07895H06R[b4b5b6X18115C115E115I'F'F\J^18P;P=P@O2b311@E11@I'F,FF%@K/7SRF#?,9QRQAQPSKf7R\5R:S05,3:/7S/9FRF+05R],^AS0610;2#2X<810]=S07%2;R^X97R_10Q=10F='UP_P61U5;#2%2@%25R`':Ra[1:`^1U@5#2[R`1U=@#2\a2045;P;n2001000000120000000X@7X?7P`^@7^?7P;%@SR`/7PRa#?R^,9O/02RbAQNPSRc=R:K,3:Rd/7PRe/9a/02Rf%2b%2f10O210^2Rg'5P_PG11PCRh11SH':S08%<P11S0':S09%@PRi/7N#?/0<S0:#]P\11NCRj11PH':RkP6f<Rl/1CS0;11NHS0<%@lRmf=Rn'7#?/=\RoP;f>Rp/1CRqPCf?Rr/1HRsf@Rt#@/75#?/=NRu[X:811pHRvPH%@;Rw/7C#?/=NX;8PGPh11PE11PI'FS0=%@H/7C#?RH/=NP\PC1=H5^2JX78Rx1LCC?4C0Ry10HC#IW2PlP;PNEJX0jP;O111NE11NI'FRzPG11lES0>11lIS0?1=HnP;11nER{PEPx1LCE?4E0R|10HE#IW2PpP;PnEJW0P;O111nIR}PIPx1LCI?4I0Rx10HI#IW2PpP;PnEJW0P;O1n200100000021000010000W0P;O1n200100000021000011000PrP;DCW0PrP;DCW0P5P;O2n2001000000121000000W0P;O1%<N11P0':RHP6%<lS0@11N0S0APoP;%<pRoP8P911r0R~Pu[X:811p0RuP017w9#?/=NX;8PGPhQ0=%@0/79#?Rh/=NP\PC1=h5^2JX78Rw10hC#IX2yPlP;PNEJX0jP;O1PGQ0>Q0?1=hnP;PEPw10hE#IX2|PpP;PnEJX0{P;O1PIPw10hI#IX2xPpP;PnEJX0}P;O1n200100000021000010000X0zP;O1n200100000021000011000PrP;DCW0PrP;EPW0P5P;O2n2001000000121000000W0P;O1n200100000021100011000%]gP7PB13An/0LRg/5;#2X9713AlRz/0<$03Q0:P;E\b0PbATO^2D>10e2R^10a2'5P_P7P^PB1;2PRb,0dP_13:cR}13:KRx'9Rh1;<NRI,0;Rw#2X<810}b10xb'5R{P_1DOP/9`R`,^:13:S/0I,5w#2X<8PGQ08Q09%8IRGQ01#BRw,OIRO':P\P6Q0;Q0<1;\nRn#8R\?4nwR_P;PC1;N5R|#8?4|wR|\sX:8PMPRPTPUPVPXPY1f89RsAZ81WRW'N,6V%HwRE,MW,6V5GVCAPZP[b4b5b6X181;5CRC#8?4Cw\J^18P;PNPPO2RCb3X0vPrP;DCX0qP5P;O2n2001000000121000000X0kP;O1P6Q0@Q0AP_P;P8P9P|\~X:8PMPRPTPUPVPXPYAZ81sR~,Ns,6V1M~E,6V5GVCAPZP[b4b5b6X181;59R9#8?49w\J^18PCb3X0uPrP;EPX0oP5P;O2n2001000000121000000X0HP;O1n200100000021100011000%8b?4bw1DzNRH/9iRo/0IRr13:P1;LlRu'0RC,5;#2X97R910HIR~10iI'5P91YINR9,0z%@NR|/0u,5;/5C#2X97P6PGPO1YulRC,1LP;1;Kp/OwR_PMPRP81a8@P5%y8CxRkPU1g8DRD9Z81Rq=w8D,S1,6VPZP[b4b5b6X18X881;;5RD/Y5,1;^18^88P;PtPPO2b3W=X0\P5P;O2n200100000012000000011<9P8PL13Ap/0;10mnRm'513:N/0nRn'5#2X<8P7PB15;m/5n#2X971V7BRnPgP2PLP<O2EPPCP;E\b0P~PzPNPIP6PGPO%8uRzP;PMPRPkPUPV1Nsq,6VR~PYP~CAPZP[b4b5b6X18X88%8D1;5@#8RC[^18^88P;PtPPP@O3b3X=_X0\P5P;O2n2001000000120000000CuD>PrATHiID>1^:o/0IP:PoPIP6PGPOA4zuwP;PMPRPkPUPV1MqE,6VRqPYPVP~PYAGV~qCACAPZP[b4b5b6X18X881ODw1;@=RD#8?4Dw\C[^18^88P;PtPPP5P@O4b3X=_X0\P5P;O2n2001000000121000000%b:94GIeC`D>bH1c:`,3:1d:`DC%2{e10hbAT}xbD>PdAt:cKDCP^PdPPP2p-0RdPMPRPTPUPVQ04PVP>P3P3P4P=Er5GVPY1Ns1,6VRsCAPZP[b4b5b6X18W>Q03/:5%85R4[^18^>dP;1O<0P<P2O3b3C{D>C|%]^P7PB17|l/0L,5;#2X97PnAQlNP=R:S,3:/7N/0<P;E\b0PfATea2D>C}O3b0Q07A~QF=D>Q06/0=PAP]P=PMPRPTPUPVPXPY%B?R?#H,M1,6V9GVsCAPZP[b4b5b6X18A445?\J^18P;P2P=O2b3%8=%bA74=eC`D>1cA],3A1dA]DCPPPSPKQ05C[,3A/0=#2ebGbDX2JX78O2b0P<P2P=AQ<2==R:@C[#ieWFWEWCX;8X:8WAP=P@P5P;O4WCX;8X:8WAo"). Qed.

(* [comment removed for export] *)
Lemma exec_csr_fz op rd operand writes csr c :
  frm_zero (c_fcsr c) -> op_clear op || negb (csr_frm_unsafe writes csr) = true -> eff_fz (exec_csr op rd operand writes csr c).
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "p'0h02SFh11Hh21bi001bh31ri011rh41ci021ch53csrh62opi032oph77operandh82rdh96writesi046writesh:2E1h;2E2h<2E3h=2FZh>2N1h?2N2h@2N3hA1ei051ei063leni072loi081ni091pi0:1xp;1p;2p;4p;3p;6p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0p1004Np4p710R8p8P0p1004ep4p710R9p8P0p1005Ep4p710R0p8p1005bp4p70R:P8p8P:P1p8P:P2p8P:g006RR8p4p710R;p8P:p1006np4p710R<p8P:p1007Lp4p7210R=p8P:P4p8P:P3p4p710R3p8P:p1007ip4p710R>p8P:p1008Yp4p710p8P:P6p8P:P7p8P:p1009:p4p710p8p1009Wp4p710R:P;p8P:P6p8p100:4p4p70R?P1p8P?P2p8P?p100:bp4p7210p8P?P;p8P?p100;>p4p710p8P?p100<4p4p7210p8P?P:p8P?P<p8P?p100<cp4p710p8P?P=p8P?p100=^p4p710p8P?p100>Xp4p710p8P?P4p8P?P3p8P?p100?Tp4p710p8P?P>p8P?P6p8P?p100@Np4p7210p8P?P7p8P?P0p8P?p100ABp4p710p8P?p100BHp4p7210R@p8P?p100BeRAp4p7210RBp8P?p100CBp4p7210p8p100CaR?p4p710RCp100Dcp4p710RDp8PCP0p8PCPAp4p710RAp8P?p4p7210R?P:p8P?P6p8P?P0p8P?PBp8p100EEp4p710R:p100FCp4p710REp8P:p100F_p4p710RFp8P:PDp8P:P9p8p100G>RDp4p710RGP1p8PGP2p8PGPEp8PGPFp8PGP4p8PGP3p8PGP6p8PGP7p8PGPCp8PGP:p8PGP9p8PGP0p8PGPAp8PGp100HAp4p710RGp8PDp4p7210RDP1p8PDP2p8PDP4p8PDP3p8PDP>p8PDP7p8PDP?p8PDP0p8PDPBp8p100H`p4p7210RBP;p8PBP<p8PBP=p8PBP6p8PBp100ILp4p710p8PBp100Iip4p710p8PBp100K0p4p710p8p100L:p4p710P6p8p100LUp4p70RBP1p8PBP2p8PBP;p8PBP<p8PBP=p8PBP4p8PBP3p8PBP>p8PBP6p8PBP7p8P@P6p8p100MKp4p710R@p100NJp4p710p8P@P9p8PGP;p8PGP6p8g00OBj1?Tg00Ogj1ZTg00PLj1HTg00Pjj1FTg01S:j16Tg01T=j2_Tg01UFj1NTg00`mj27Tg00k:j1ETg01Udj2MTg00aWj29Tg01VFR6j2RTg01ViRGj2dTg00TnR;j1bTg01WIj2QTg01Wkj4UTg00b4j1^Tg00SQj10Tg01ISj3>Tg01XKj33Tg01Xoj2:Tg01J?j35Tg00V9j3ATg01YTj1BTg01Z<j1GTg01Zdj1=Tg00fij1STg01Mmj24Tg01[ej3]Tg01\nj3LTP5j6OTg01:]j1PTP8j6eTg01^0j2KTg00mNj2JTg00T:j3DTg00TTj2ITg01>`j4YTg01^Oj3cTg01^ij6TTg01_lj3aTg01`Fj6`Tg01Jdj4WTg01a1j2XTg00oGj2[Tf0R8#0#Sp=8g00WnR5f1R9/48g01EZR@3Dp=<g00_fR7?D98p=2P7P7g01B6RBP8CUp=Vf4R>f3R3f2R4P9CW/X8p=;A>9B8p=CP3PBP4P9CW/X8p=@1[98#N,44=D5@p=11[98#Np=\g01a]R=g00V`R<#?R2#ZR1#H#FRD%?2#?R0#?#?R?#?#HRA#FR:%Z<RC#?#?#HRF#FREg00WERH%88f6RI#61_34#N'<17F3RJ%E<R<'M12J<19J<RK'R17F>/9<P5P6f5RL,7F/2<P;1d77RMg01bIRNP5%bMROP9%E1R1#V,QMRPP5POf7RQ,7FRR%E2R2'9RSP7P7P1%ECRCCU,QMRTP5PO19RCRU%E0R0#V,QMRV%^MRWn0100000020000n0100000020000n0100000020000PGP7P7PNP8f=RXf9RY#0RZ?>98R[P5PHf;R\PZP9P8P=P:f>RZf<R]A3A[]1:A]95A[n011030003000000PYD;PYn01104000200003A#Bn2001109000120107106%GIn10110:00021010900#=P917FI/2<R<%H?#FR?P5PHf8R[%0IR^P1P=P:P\PY1C^1R^=3AY1:AY95A^n011030003000000PIC@PIn0110400020000R_#0%S8X2?R`P5%6]17F[Ra/92Rb19aC'4718P5PHP9%0[RaP1P=P:PXP\1Ca1Ra=3A\1:A\95Aan011030003000000P[C@P[n0110400020000#8]0P[%6\Ra14SURU71@%0QRcP=P:P]f:Rd1Cc1Rc=3Ad1:Ad95Acn011030003000000;]IW0g01BTRc=1aUPIW0n0110000020000P>O1AAd^_RU#0ALd^_EO%BU#=eW:P8O1%P<1MR212R2/RSPbP5P617FY/22f?Rb#6RS17F\/9CRR,4971]P;PMPNP5POP4PTP5PO17F]R</9CRUPVPWn0100000020000n0100000020000PGP7P7PNP8fBR_%0ZR^?>98RaP5PHf@ReP^P9P8P=P:fCRffARgA3Aag1:AgRh95Aan011030003000000PZD;PZn01104000200003A#Bn2001109000120107106%G\n10110:00021010900#=]0P917Fd/22Ra14@R91S]P?P5PHPX%0\RiP1PCP=P:PePZA>i1CRi=3AZ1:AZ95Ain011030003000000P\D;P\n0110400020000Rj#0P`P5%6g17FX/9CRk,4@Rl718P5PHP9%0XRmP1PCP=P:P_PeA>m1CRn=3Ae1:AeRo95AnRnn011030003000000PXD;PXn0110400020000#8]0PX%6eRp14@URq71@P=%68Rr17FZRs/9C,4@71@P^P1PCP=P:P9PgA>^1CRt=3AgRuA5Athn011030003000000PZD;#8]0Pgg01c1#6Rt1\@lRl'<P5PcP5p-0P8g01H4Rhg01c]n0110000020000XA5g01d9RvP@P8EeRwPhP^P1PCPgPZD;#8/K8b1W0g01dU#6Rx/<lPwPhP^P1PCPuPZD;#8/K8b1W0g01eA#6RZ/<lPmP1PCPo1211Ro12CCRl'JAD71B12C0'JPoPl1I711I7CCY3cP]ETPmP1PCPnPXD;#8eW0n011020003000000P8O1W0A1pcqP\W0n0110000020100P8O1AAbijR\#0ALbijEO%B\#=eW0W;P8O1%Pa14cR91S]1M<C12<C/RUPkP5P612sCfDRs#6R614c971gP;PMPNP5POP4PVPWn0100000020000PGP7P7PNP8fGRk%0fRU?>98R<P5PHfERSPUP9P8P=P:fHfFR]A3A<]1:A]RR95A<n011030003000000PfD;Pfn01104000200003A#Bn2001109000120107106%Gen10110:00021010900#=]0P917Fb/2CRb14c@RF916gP?P5PHP_%0eR?P0P=P:PSPf1C?0R?=3Af1:Af95A?n011030003000000PeC@Pen0110400020000R<#0P`P5%6]?18FP5PHP9%0_R`P0P=P:PkPS1C`0Rk=3AS1:ASRa95AkRkn011030003000000P_C@P_n0110400020000#8]0P_%6SRS1\@FR@'<P=1<r@PUP0P=P:P9P]1CU0Rr=3A]R\A5ArRn011030003000000PfC@#8]0P]1<t@PwPhPUP0P]PfC@#8/K8b1W01<x@PwPhPUP0P\PfC@#8/K8b1W01<Z@P`PBP0PaAD7B1120C'JAD7BBR11200Ra'JP1Pa1I7B1I70CY3aPgETP`P0PkP_C@#8eW0n011020003000000P8O1W0A1ScFPeW0n0110000020100P8O1AAs?<Re#0ALs?<EO%Be#=eW0W<P8O1%Pb14cc916gPvW0W@P8O1n10210010100021110510108P4O1b2b3W0W?P8O1n10210010100021110511108PIO1b2b3W>P8O1n10210010100021110511108b2b3P;PMPNP5POPKPPP5PO19J2PTP5PO19JCPVPWn0100000020000n0100000020000n0100000020000PGP7P7PNP8%0LRN?>98R7P5PHPQPNP9P8P=P:PdP[A3A7[1:A[95A7n011030003000000PLD;PLn01104000200005AY#Bn2001109000120107106%G4n10110:00021010900#=ePQPIPLP>P3P4E`#=eW0W=X4HX5EX95X7:X8DX6=PLP>P3P4P9P8O6W4W5X95W7W8W6o"). Qed.

Lemma exec_fz (sz : word) (i : instr) (c : core) :
  frm_zero (c_fcsr c) -> instr_frm_safe i = true -> eff_fz (exec sz i c).
Proof.
  intros FZ SF. destruct i; cbv beta iota zeta delta [exec load_val store_val]; try (fz_tree FZ).
  - cbn [instr_frm_safe csr_writes] in SF. apply exec_csr_fz; [fz_core FZ| exact SF].
  - cbn [instr_frm_safe csr_writes] in SF. apply exec_csr_fz; [fz_core FZ| exact SF].
Qed.

(* [comment removed for export] *)
Lemma interp_fz segs : forall e m rep, eff_fz e -> interp_eff_accesses segs e m = MachineOk rep -> frm_zero (c_fcsr (fst (@access_value _ rep))).
Proof.
  induction e as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m rep FZ H; cbn [interp_eff_accesses] in H; try discriminate.
  - injection H as <-. exact FZ.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|lazymatch type of H with context [if ?b then _ else _] => destruct b end; discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r| | ] eqn:E; try discriminate.
    injection H as <-. cbn [access_value fst]. exact (IH _ m r (FZ _) E).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r| | ] eqn:E; try discriminate.
    injection H as <-. cbn [access_value fst]. exact (IH _ r FZ E).
Qed.

(* [comment removed for export] *)
Lemma decode_exec_fz segs st w rep :
  frm_zero (ms_fcsr st) -> word_frm_safe w = true -> decode_exec_accesses segs st w = MachineOk rep -> frm_zero (ms_fcsr (@access_value _ rep)).
Proof.
  intros FZ SF H. unfold decode_exec_accesses in H. unfold word_frm_safe in SF.
  destruct (is_ecall w); [injection H as <-; exact FZ|].
  destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
  destruct (interp_eff_accesses _ _) as [r| | ] eqn:E; try discriminate.
  pose proof (interp_fz segs _ _ r (exec_fz (Z_to_bv 64 isz) i (Core (ms_regs st) (ms_fregs st) (ms_pc_val st) (ms_fcsr st) (ms_resv st)) FZ SF) E) as FZ'.
  destruct (@access_value _ r) as [c m'] eqn:Er. cbv beta iota zeta in H. injection H as <-. cbn [access_value ms_fcsr fst] in *. exact FZ'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma find_segment_In : forall l a n seg, find_segment l a n = Some seg -> In seg l.
Proof.
  induction l as [|s l IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (_ && _); [injection H as <-; left; reflexivity| right; exact (IH _ _ _ H)].
Qed.
Lemma find_segment_range : forall l a n seg, find_segment l a n = Some seg ->
  Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction l as [|s l IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.leb_spec (Z.of_N (seg_base s)) a) as [L1|L1]; destruct (Z.leb_spec (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [L2|L2]; cbn [andb] in H;
    first [injection H as <-; split; assumption | exact (IH _ _ _ H)].
Qed.

Section Generic.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis no_wx : forall seg, In seg segs -> seg_executable seg && seg_writable seg = false.

Lemma code_read_ov_none m a n : code_read_ov segs m a n = None.
Proof.
  unfold code_read_ov. destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:E; [|reflexivity].
  rewrite (no_wx seg (find_segment_In _ _ _ _ E)). reflexivity.
Qed.
Lemma fetch_word_ov_none m a : fetch_word_ov segs m a = None.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) ["Generic"] "p'0h01ah11mh21bi001bh31oi012b0i022b1i032b2i042b3i051li062l0i072l1i082l2i092l3i0:2l4i0;1xp;1p;2p;4p;3p;6p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0p1004Np4p710R8p8P0p1004ep4p710R9p8P0p1005Ep4p710R0p8p1005bp4p70R:P8p8P:P1p8P:P2p8P:p1006Rp4p710R8p8P:p1006np4p710R;p8P:p1007Lp4p7210R<p8P:P4p8P:P3p4p710R3p8P:p1007ip4p710R=p8P:p1008Yp4p710p8P:P6p8P:P7p8P:p1009:p4p710p8p1009Wp4p710R:P8p8P:P6p8p100:4p4p70R>P1p8P>P2p8P>p100:bp4p7210p8P>P8p8P>p100;>p4p710p8P>p100<4p4p7210p8P>P:p8P>P;p8P>p100<cp4p710p8P>P<p8P>p100=^p4p710p8P>p100>Xp4p710p8P>P4p8P>P3p8P>p100?Tp4p710p8P>P=p8P>P6p8P>p100@Np4p7210p8P>P7p8P>P0p8P>p100ABp4p710p8P>p100BHp4p7210R?p8P>p100BeR@p4p7210RAp8P>p100CBp4p7210p8p100CaR>p6051001RBp100Dcp4p710RCp8PBP0p8PBP@p4p710R@p8P>p60521000R>P:p8P>P6p8P>P0p8P>PAp8p100EEp6051000R:p100FCp4p710RDp8P:p100F_p4p710REp8P:PCp8P:P9p8p100G>RCp6051001RFP1p8PFP2p8PFPDp8PFPEp8PFP4p8PFP3p8PFP6p8PFP7p8PFPBp8PFP:p8PFP9p8PFP0p8PFP@p8PFp100HAp4p710RFp8PCp60521000RCP1p8PCP2p8PCP4p8PCP3p8PCP=p8PCP7p8PCP>p8PCP0p8PCPAp8p100H`p4p7210RAP8p8PAP;p8PAP<p8PAP6p8PAp100ILp4p710p8PAp100Iip4p710p8PAp100K0p4p710p8p100L:p4p710P6p8p100LUp4p70RAP1p8PAP2p8PAP8p8PAP;p8PAP<p8PAP4p8PAP3p8PAP=p8PAP6p8PAP7p8P?P6p8p100MKp6051000R?p100NJp4p710p8P?P9p8PFP8p8PFP6p8g00OBj10Tg00PLj11Tg00Pjj13Tg00TnR6j12Tg011ERFj1BTg00b4j19Tg00`mj28Tg00k:j1<Tg03dHj26Tg00aWj27Tg01UFj15Tg03dhj4;Tg01WIj2:Tg00T:j34Tg00TTj2ATg03cDj4@Tg03e[j3=TP5j6>Tg03fgj3?Tg00V`#0R5#0R8#0R9#0#0R?#0#1R7#3RA%19#3R9#2[R=%B9R3#2R4%93%1?#3R?#2R<g00WnR;P<f1R2,87%<5R5'6g01B6R1'7#5%9?RCP6P3P<f0R3PFP9P<P3PCPFP9P<P3PCPFP9P<P3PCPFP9P<P3PCPFP9P<P3P2f3f5f7C;,:?PCn1011090002002010010:n10110800020020104109n10110700020020103108n10110600020020102107n10110500020020101106PCn10110;00021010500n0100000020001;4CX341873/65/71#5P;P;P;P<P3PCPCn0100000020000=4<CP31A<CR;P;n0110000020000b2p,4segsR;P2P3%18R8C@A=238E>A?;23=4<CeX0AX1=P2P3O2X0AW1o"). Qed.
Lemma fetch_half_any_eq m a : fetch_half_any segs m a = fetch_half segs a.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) ["Generic"] "p'0h01ah11mh21oi001oh31bi011bi022b0i032b1i041hi051li062l0i072l1i082l2i091xp;1p;2p;3p;4p;6p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0p1004Np4p710R8p8P0p1004ep4p710R9p8P0p1005Ep4p710R0p8p1005bp4p70R:P8p8P:P1p8P:P2p8P:p1006Rp4p710R8p8P:p1006np4p710R;p8P:p1007Lp4p7210R<p8P:P4p8P:P3p4p710R3p8P:p1007ip4p710R=p8P:p1008Yp4p710p8P:P6p8P:P7p8P:p1009:p4p710p8p1009Wp4p710R:P8p8P:P6p8p100:4p4p70R>P1p8P>P2p8P>p100:bp4p7210p8P>P8p8P>p100;>p4p710p8P>p100<4p4p7210p8P>P:p8P>P;p8P>p100<cp4p710p8P>P<p8P>p100=^p4p710p8P>p100>Xp4p710p8P>P4p8P>P3p8P>p100?Tp4p710p8P>P=p8P>P6p8P>p100@Np4p7210p8P>P7p8P>P0p8P>p100ABp4p710p8P>p100BHp4p7210R?p8P>p100BeR@p4p7210RAp8P>p100CBp4p7210p8p100CaR>p6051001RBp100Dcp4p710RCp8PBP0p8PBP@p4p710R@p8P>p60521000R>P:p8P>P6p8P>P0p8P>PAp8p100EEp6051000R:p100FCp4p710RDp8P:p100F_p4p710REp8P:PCp8P:P9p8p100G>RCp6051001RFP1p8PFP2p8PFPDp8PFPEp8PFP4p8PFP3p8PFP6p8PFP7p8PFPBp8PFP:p8PFP9p8PFP0p8PFP@p8PFp100HAp4p710RFp8PCp60521000RCP1p8PCP2p8PCP4p8PCP3p8PCP=p8PCP7p8PCP>p8PCP0p8PCPAp8p100H`p4p7210RAP8p8PAP;p8PAP<p8PAP6p8PAp100ILp4p710p8PAp100Iip4p710p8PAp100K0p4p710p8p100L:p4p710P6p8p100LUp4p70RAP1p8PAP2p8PAP8p8PAP;p8PAP<p8PAP4p8PAP3p8PAP=p8PAP6p8PAP7p8P?P6p8p100MKp6051000R?p100NJp4p710p8P?P9p8PFP8p8PFP6p8g00OBj10Tg00PLj12Tg00Pjj14Tg00TnR6j13Tg03glj2?Tg01WIj28Tg03hnj37Tg00T:j31Tg00TTj26Tg011ERFj1;Tg00b4j15Tg03j3j29Tg03cDj4:Tg03e[j3>TP5j6=Tg03jfj3<Tg00V`#0R5#0#0R8#0R9#0#0#2#4R?%28#4R8#3[R7p,4segsRAf0R='?R3%29#4R9#3R4P6P9P6P9P4P=189=R<f3R;f2R257An10110900021010400=14=P=164<X39P=O1%;8R<#3R1%5<P6P<P4P=PFP8P4P=%59R<PFP8P4P=P<PFP8P4P=f1R8/9;,89P<n10110700020020101108n10110600020020103107n10110500020020102106P<n10110900021010500=14<X21164<PAP2P8%25R5C:A>285E=A7A28=14<en10110000021010101b2A<A8==143eX0?X17P8P=O2X0?W1o"). Qed.
Lemma fetch_tail_any_eq m a : fetch_tail_any segs m a = fetch_tail segs a.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) ["Generic"] "p'0h01ah11mh21oi002h0i012h1i021xp;1p;2p;4p;3p;5p;6p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0p1004Np4p710R8p8P0p1004ep4p710R9p8P0p1005Ep4p710R0p8p1005bp4p70R:P8p8P:P1p8P:P2p8P:p1006Rp4p710R8p8P:p1006np4p710R;p8P:p1007Lp4p7210R<p8P:P4p8P:P3p4p710R3p8P:p1007ip4p710R=p8P:p1008Yp4p710p8P:P6p8P:P7p8P:p1009:p4p710p8p1009Wp4p710R:P8p8P:P6p8p100:4p4p70R>P1p8P>P2p8P>p100:bp4p7210p8P>P8p8P>p100;>p4p710p8P>p100<4p4p7210p8P>P:p8P>P;p8P>p100<cp4p710p8P>P<p8P>p100=^p4p710p8P>p100>Xp4p710p8P>P4p8P>P3p8P>p100?Tp4p710p8P>P=p8P>P6p8P>p100@Np4p7210p8P>P7p8P>P0p8P>p100ABp4p710p8P>p100BHp4p7210R?p8P>p100BeR@p4p7210RAp8P>p100CBp4p7210p8p100CaR>p6051001RBp100Dcp4p710RCp8PBP0p8PBP@p4p710R@p8P>p60521000R>P:p8P>P6p8P>P0p8P>PAp8p100EEp6051000R:p100FCp4p710RDp8P:p100F_p4p710REp8P:PCp8P:P9p8p100G>RCp6051001RFP1p8PFP2p8PFPDp8PFPEp8PFP4p8PFP3p8PFP6p8PFP7p8PFPBp8PFP:p8PFP9p8PFP0p8PFP@p8PFp100HAp4p710RFp8PCp60521000RCP1p8PCP2p8PCP4p8PCP3p8PCP=p8PCP7p8PCP>p8PCP0p8PCPAp8p100H`p4p7210RAP8p8PAP;p8PAP<p8PAP6p8PAp100ILp4p710p8PAp100Iip4p710p8PAp100K0p4p710p8p100L:p4p710P6p8p100LUp4p70RAP1p8PAP2p8PAP8p8PAP;p8PAP<p8PAP4p8PAP3p8PAP=p8PAP6p8PAP7p8P?P6p8p100MKp6051000R?p100NJp4p710p8P?P9p8PFP8p8PFP6p8g00OBj10Tg00PLj12Tg00Pjj13Tg00TnR6j14Tg03glj21Tg00`mj27Tg00k:j1>Tg03dHj2=Tg00aWj25Tg01UFj1<Tg00b4j1DTg03klj4CTg00Ogj1BTg03Lej3ATg01g@j39Tg03jfj38Tg01gej5@Tg01WIj2?Tg00T:j36Tg00TTj2GTg03lWj2:TP5j6;Tg03mcj3FTg03nij2ETg00V`R5#0RF#0#0R8#0R9#0R?#0#2R7#3RA%28#3#4[R8%29R9#3R=#4R3p,4segsR4f0R<'1R;%2?R?#3R2#4R1g00WnRCP1f1R0,77%>FR>'=g01B6R@'5#<R:%D2RBP6P=P1P<PCP1%2FRFP9g02bFPFP<CC'7%B5#>'5R5P6P=P1f3f2g01d9RF9A7>RE597RD584P?P9P9P<P0D@,?2RGPBn10110200021010100P?P9P9AA9@FP<D@,?2R2n0100000020000PBn10110200021010000n0100000020001PCP1P:PBP6P=P11140RFPCP1P5P6P=P1114DPGPBn10110200021010100P2n0100000020000PBn10110200021010000n0100000020001RD36X23P3A97<ER9,14PCP1P:PBP6P=P1PFPCP1P5P6P=P1P0PGPBn10110200021010100P2n0100000020000PBn10110200021010000n0100000020000=61DX23PCP1177</=>/5@#<PBP6P=P1P;PCP1P5P6P=P1A970E,14PGPBn10110200021010100P2n0100000020000PBn10110200021010000n0100000020001,G1A84091:09E;A840<1:0<E;AF40<1E4<561eX0AX18P0P<O2X0AW1o"). Qed.

(* [comment removed for export] *)
Lemma code_read_seg a n bs : code_read segs a n = Some bs ->
  exists seg, In seg segs /\ seg_executable seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + Z.of_N n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  unfold code_read. destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:E; [|discriminate].
  destruct (seg_executable seg) eqn:X; [|discriminate]. intros _. exists seg.
  split; [exact (find_segment_In _ _ _ _ E)|]. split; [exact X|]. exact (find_segment_range _ _ _ _ E).
Qed.
Lemma fetch_word_seg a w : fetch_word segs a = Some w ->
  bv_unsigned a mod 2 = 0 /\ exists seg, In seg segs /\ seg_executable seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + 4 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  unfold fetch_word. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  destruct (code_read segs a 4) as [bs|] eqn:C; [|discriminate]. intros _. split; [exact E|]. exact (code_read_seg a 4 bs C).
Qed.
Lemma fetch_tail_seg a w : fetch_tail segs a = Some w ->
  bv_unsigned a mod 2 = 0 /\ exists seg, In seg segs /\ seg_executable seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + 2 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  unfold fetch_tail. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  unfold fetch_half at 1. destruct (code_read segs a 2) as [bs|] eqn:C; [|discriminate]. intros _. split; [exact E|]. exact (code_read_seg a 2 bs C).
Qed.

(* [comment removed for export] *)
Definition ok_at (a : Z) : bool :=
  (match fetch_word segs (Z_to_bv 64 a) with Some w => word_frm_safe w | None => true end)
  && (match fetch_tail segs (Z_to_bv 64 a) with Some w => word_frm_safe w | None => true end).
Fixpoint scan1 (f : nat) (a : Z) : bool := match f with O => true | S f' => ok_at a && scan1 f' (a + 2) end.
Fixpoint scan2 (g f : nat) (a : Z) : bool := match g with O => true | S g' => scan1 f a && scan2 g' f (a + 2 * Z.of_nat f) end.

Lemma scan1_sound : forall f a0, scan1 f a0 = true -> forall a, a0 <= a < a0 + 2 * Z.of_nat f -> (a - a0) mod 2 = 0 -> ok_at a = true.
Proof.
  induction f as [|f IH]; intros a0 H a Ha Hm; [cbn [Z.of_nat] in Ha; lia|].
  cbn [scan1] in H. apply andb_true_iff in H as [H0 H1].
  destruct (Z.eq_dec a a0) as [->|NE]; [exact H0|].
  apply (IH (a0 + 2) H1); [lia|]. replace (a - (a0 + 2)) with (a - a0 + (-1) * 2) by lia. rewrite Z.mod_add by lia. exact Hm.
Qed.
Lemma scan2_sound : forall g f a0, scan2 g f a0 = true -> forall a, a0 <= a < a0 + 2 * Z.of_nat f * Z.of_nat g -> (a - a0) mod 2 = 0 -> ok_at a = true.
Proof.
  induction g as [|g IH]; intros f a0 H a Ha Hm; [cbn [Z.of_nat] in Ha; lia|].
  cbn [scan2] in H. apply andb_true_iff in H as [H0 H1].
  destruct (Z_lt_le_dec a (a0 + 2 * Z.of_nat f)) as [LT|GE].
  - exact (scan1_sound f a0 H0 a ltac:(lia) Hm).
  - apply (IH f (a0 + 2 * Z.of_nat f) H1); [lia|]. replace (a - (a0 + 2 * Z.of_nat f)) with (a - a0 + (- Z.of_nat f) * 2) by lia.
    rewrite Z.mod_add by lia. exact Hm.
Qed.

(* [comment removed for export] *)
Theorem fetch_safe_of_scan (xlo xsz : Z) (g f : nat) :
  (forall seg, In seg segs -> seg_executable seg = true -> Z.of_N (seg_base seg) = xlo /\ Z.of_N (seg_size seg) = xsz) ->
  xlo mod 2 = 0 -> xsz <= 2 * Z.of_nat f * Z.of_nat g -> scan2 g f xlo = true ->
  forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> word_frm_safe w = true.
Proof.
  intros XS XE COV SC a w H.
  assert (R : bv_unsigned a mod 2 = 0 /\ xlo <= bv_unsigned a < xlo + xsz).
  { destruct H as [H|H]; [destruct (fetch_word_seg a w H) as (E & seg & IN & X & B1 & B2)| destruct (fetch_tail_seg a w H) as (E & seg & IN & X & B1 & B2)];
      destruct (XS seg IN X) as (EB & ES); split; [exact E| lia| exact E| lia]. }
  destruct R as (EA & RA).
  assert (OK : ok_at (bv_unsigned a) = true).
  { apply (scan2_sound g f xlo SC); [lia|]. rewrite Zminus_mod, EA, XE. reflexivity. }
  unfold ok_at in OK. rewrite Z_to_bv_bv_unsigned in OK. apply andb_true_iff in OK as [O1 O2].
  destruct H as [H|H]; [rewrite H in O1; exact O1| rewrite H in O2; exact O2].
Qed.

(* [comment removed for export] *)
Hypothesis fetch_safe : forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> word_frm_safe w = true.

Theorem step_fz : forall s s', RiscvSemantics.step segs s = MachineOk s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof.
  intros s s' H FZ. unfold RiscvSemantics.step, step_accesses in H.
  destruct (fetch_word segs (ms_pc s)) as [w|] eqn:F1.
  - destruct (decode_exec_accesses segs s w) as [r| | ] eqn:E; try discriminate. cbn [drop_access_report] in H. injection H as <-.
    exact (decode_exec_fz segs s w r FZ (fetch_safe _ _ (or_introl F1)) E).
  - rewrite fetch_word_ov_none, fetch_tail_any_eq in H.
    destruct (fetch_tail segs (ms_pc s)) as [w|] eqn:F2.
    + destruct (decode_exec_accesses segs s w) as [r| | ] eqn:E; try discriminate. cbn [drop_access_report] in H. injection H as <-.
      exact (decode_exec_fz segs s w r FZ (fetch_safe _ _ (or_intror F2)) E).
    + exfalso. unfold fetch_failure in H.
      (* #38 gave fetch_failure a LEADING vdso_text_at arm.  The two destructs below cannot
         absorb it: neither [negb _] nor [_ || _] unifies with [vdso_text_at _ _], so the first
         [discriminate] would meet a goal that is still an if-match.  Donor, THIS TREE, same
         class, already repaired: Mh_0036.v:3905-3910. *)
      destruct (vdso_text_at segs (ms_pc s)); [discriminate|].
      destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

Theorem msteps_fz : forall s s', msteps segs s s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof.
  intros s s' H. induction H as [ms| ms ms' ms'' P ST MS IH]; intros FZ; [exact FZ|].
  apply IH. exact (step_fz ms ms' ST FZ).
Qed.

(* [comment removed for export] *)
Corollary msteps_fz_mkst (fx fx' : FPState) R R' pc pc' M M' :
  msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs)) -> frm_zero (@fp_csr fx) -> frm_zero (@fp_csr fx').
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) ["Generic"] "h01Mh12M'h21Rh32R'h42fxh53fx'h62pch73pc'h82FZh92MSp;1p;2p;5p;3p;4p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p6051001RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p60521000R=P9p8P=P5p8P=P0p8P=P@p8p100EEp6051000R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp6051001REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp60521000RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8g00H`R@p4p7210RBP7p8PBP:p8PBP;p8PBP5p8PBp100ILp4p710p8PBp100Iip4p710p8PBp100K0p4p710p8p100L:p4p710P5p8p100LUp4p70RBP1p8PBP2p8PBP7p8PBP:p8PBP;p8PBP4p8PBP3p8PBP<p8PBP5p8PBP6p8P>P5p8p100MKp6051000R>p100NJp4p710p8P>P8p8PEP7p8PEP5p8g00OBj10Tg00Ogj1;Tg00PLj12Tg00Pjj13TP@j2:Tg00Tnj19Tg04bjj17Tg04c_j51Tg04^hj35Tg04dQj16Tg00fij14Tg04eEj48Tg04fIR@g00V`#0R5#;#2%05#0R5#0#0#0#2#3RE':R7%25#3#9\ER5p,4segsR8f7R>f5R6f3RBf1R<%78R8D1f6R3f4R4f2R;f0R:P8D135f8R2#6#4f9P>P6PBP8D1P2P3P4P;P8D1P<P:C8W8W9X15X05X7EX6EX37X27X5@X4@P>P3P6P4PBP;P<P:O8X15W0X7EX6EX37W2X5@W4o"). Qed.
End Generic.
(* [comment removed for export] *)
Lemma safe_of_coarse (w : bv 32) : FrmKeep.FRM.word_frm_safe w = true -> word_frm_safe w = true.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKeepC ()) [] "p'0h02rdi002rdh13rs1i013rs1h22opi022oph33rs2i033rs2h43immi043immh53fmti053fmth62rmi062rmh72aqi072aqh82rli082rlh92w0h:1Hh;2H0h<2b1h=2b2h>3csri093csrh?5shamti0:5shamth@3sz0hA1wi0;1whB1ci0<1chC3diri0=3dirhD3dsti0>3dsthE2fmi0?2fmhF1ii0@1ihG1oi0A1ohH1pi0B1phI4predi0C4predhJ3rs3i0D3rs3hK6signedi0E6signedhL3srci0F3srchM4succi0G4succhN2szi0H2szhO4uimmi0I4uimmi0J1xi0K1zp;1p;2p;3p;4p;5p;6p;7p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710R8p8P0p1005Ep4p710R0p8p1005bp4p70R9P7p8P9P1p8P9P2p8P9p1006Rp4p710R7p8P9p1006np4p710R:p8P9p1007Lp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p1007ip4p710R<p8P9p1008Yp4p710p8P9P5p8P9P6p8P9p1009:p4p710p8p1009Wp4p710R9P7p8P9P5p8p100:4p4p70R=P1p8P=P2p8P=p100:bp4p7210p8P=P7p8P=p100;>p4p710p8P=p100<4p4p7210p8P=P9p8P=P:p8P=p100<cp4p710p8P=P;p8P=p100=^p4p710p8P=p100>Xp4p710p8P=P4p8P=P3p8P=p100?Tp4p710p8P=P<p8P=P5p8P=p100@Np4p7210p8P=P6p8P=P0p8P=p100ABp4p710p8P=p100BHp4p7210R>p8P=p100BeR?p4p7210R@p8P=p100CBp4p7210p8p100CaR=p4p710RAp100Dcp4p710RBp8PAP0p8PAP?p4p710R?p8P=p4p7210R=P9p8P=P5p8P=P0p8P=P@p8p100EEp4p710R9p100FCp4p710RCp8P9p100F_p4p710RDp8P9PBp8P9P8p8p100G>RBp4p710REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HAp4p710REp8PBp4p7210RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8p100H`p4p7210R@P7p8P@P:p8P@P;p8P@P5p8P@p100ILp4p710p8P@p100Iip4p710p8P@p100K0p4p710p8p100L:p4p710P5p8p100LUp4p70R@P1p8P@P2p8P@P7p8P@P:p8P@P;p8P@P4p8P@P3p8P@P<p8P@P5p8P@P6p8P>P5p8p100MKp4p710R>p100NJp4p710p8P>P8p8PEP7p8PEP5p8g00OBj13Tg03QBj1hTg01ViR5j2gTg00TnREj1nTg04g@j1UTg02[7j1@Tg00Ogj17Tg00PLj1<Tg00Pjj1:Tg00T:j36Tg00TTj2mTg01emj2ZTg01i8j2TTg01idj2STg01jPj3QTg01kcj4ITg01m>j5eTg01o=j4ATg022jj4?Tg024>j4CTg024jj4DTg025Vj3>Tg026jj4FTg027Vj4GTg028Bj5=Tg028nj3JTg029Zj4KTg02;0j4;Tg02;\j5MTg02=^j6NTg02>Jj7OTg00QMj1PTg01UFj14Tg04hGj29Tg04iJj2RTg01Mmj28Tg019@j2fTg04jQj2lTg01S:j1kTg04k1j2YTg01T=j2WTg01_lj3XTg02?`j4VTg00`mj2[Tg00aWj2\Tg02Bnj4]Tg02CZj4^Tg02DFj4_Tg02EYj7`Tg02K`j6aTg02O0j4bTg02PFj5cTg02RGj5LTg02S_j5BTg02VCj5HTg02Y4j4dTg02Y`j3ETg04l6j1jTg03FQj1iTf0R7#<#:p=5g00WnR8g01EZR>767p=2%U7=68>p=0%@7=68>p=1g00V`R6#3R@#3R<#3#3#3#5R3%h7g02\gR4g00_fR;'gR:#nPEP:PEP:P8P7P5P4P;P8P7f1R2#Un200110B00012010@10KR1P>n10110J00021010B00#2PEP:P8P2P5P4P;P8P7%@2REn200110B00012010@10KP>n10110J00021010B00#2[P7P5P4P;%21P5P4P;P8P2PEn200110B00012010@10K#2[P7P4%07%2E[P2%7@R@#<RE#:R5%3@R@#3#5R1A68>>1m8>UR>1Z27#0f2RB/Z2#1[eW4W0P2P7O2P>1T27#01TB2#1[eX41X05P2P7O2%7@#5P>1S27#01SB2#1[eW4X05P2P7O2%76R6#3R@#3#5R1P>AQB27#0f3R0?QB2#1[eW4X15X05PBP2P7O3g02^8%7@#5P>P0PBP2P7CI#0f4R=P0PBP2CI#1[eW4X35X15WBP0PBP2P7O4g02^jR?P>P=P0PBP2P7De#0f5R9P=P0PBP2De#1[eX41X15X05XK8W@P=P0PBP2P7O5P>P0PBP2P7CA#0P=P0PBP2CA#1[eX41X35X15X@?P0PBP2P7O4g02bdR?P>P0PBP2P7C?#0P=P0PBP2C?#1[eX41X15X05W2P0PBP2P7O4%5@P>P0PBP2P7CC#0P=P0PBP2CC#1[eW?X15X05X2?P0PBP2P7O4P>P0PBP2P7CD#0P=P0PBP2CD#1[eX35X15X05X2?P0PBP2P7O4P>A>B27#0A>0B2#1[eX41X15X05PBP2P7O3P>P0PBP2P7CF#0P=P0PBP2CF#1[eX?5X15X05X2?P0PBP2P7O4P>P0PBP2P7CG#0P=P0PBP2CG#1[eX35X15X05X2?P0PBP2P7O4%5<R<P>P=P0PBP2P7D=#0P9P=P0PBP2D=#1[eX15X05XM<XI<WEP=P0PBP2P7O5P>AJB27#0AJ0B2#1[eX41X15X05PBP2P7O3P>g02d<R<#0%1<[eP>g02dhR<#0%1<[eg02eTR<P>P0PBP2P7CK#0P=P0PBP2CK#1[eX35X15X05W2P0PBP2P7O4P>P0PBP2P7C;#0P=P0PBP2C;#1[eX35X15X05X2<P0PBP2P7O4g02f@R<P>P=P0PBP2P7DM#0P9P=P0PBP2DM#1[eX15X05X88X78W9P=P0PBP2P7O5P>P9P=P0PBP2P7EN#0f6R?P9P=P0PBP2EN#1[eX35X15X05X88X78X9<P9P=P0PBP2P7O6g02hlP>P?P9P=P0PBP2P7FO#0f7R@P?P9P=P0PBP2FO#1[eX35X15X05X88X78X9<W2P?P9P=P0PBP2P7O7g01a]R<%P2#4,90/R7#4#2g00mN1827#2%2B%22RA'fRD[%27,fA18B2#2[RA180B#2\D1l27P7n2001000000120000000X=8X<8RDPA^=8^<8R8P7%k9RA%P0#4,Y9/WB#4RC%2ARF%2C;X2O3b;W:P0PBP2P7CV#0P=P0PBP2CV#1[eX>1X15X05W2P0PBP2P7O41[E2g01B6RC'\#4,90/R7#4#2PDP8P7PA1[E0/\C#4,Y9/WB#4RC%2C=XF2O3b;W:P0PBP2P7C]#0P=P0PBP2C]#1[eX>1XO5X05X2<P0PBP2P7O4g00_;R<P>P0PBP2P7C^#0P=P0PBP2C^#1[eX41X15X05W5P0PBP2P7O4P>P0PBP2P7C_#0P=P0PBP2C_#1[eX41X35X15X5<P0PBP2P7O4g02jn%56R6P>P?P9P=P0PBP2P7F`#0P@P?P9P=P0PBP2F`#1[eW6XJ5X35X15X05X5<W2P?P9P=P0PBP2P7O7g02lDP>P9P=P0PBP2P7Ea#0P?P9P=P0PBP2Ea#1[eX66X35X15X05X5<W2P9P=P0PBP2P7O6P>P0PBP2P7Cb#0P=P0PBP2Cb#1[eX66X15X05X5<P0PBP2P7O4g02m1P>P=P0PBP2P7Dc#0P9P=P0PBP2Dc#1[eX35X15X05X5<W2P=P0PBP2P7O5g02m^P>P=P0PBP2P7DL#0P9P=P0PBP2DL#1[eX35X15X05X5<W2P=P0PBP2P7O5g02nNP>P=P0PBP2P7DB#0P9P=P0PBP2DB#1[eX35X15X05X5<W2P=P0PBP2P7O5g02o;R?P>P=P0PBP2P7DH#0P9P=P0PBP2DH#1[eX66X15X05XL?WDP=P0PBP2P7O5g02oiP>P0PBP2P7Cd#0P=P0PBP2Cd#1[eX15X05X5<WCP0PBP2P7O4P>AEB27#0AE0B2#1[eX15X05X5<PBP2P7O3n0110@000S201001042010010420100104301001011044010<1011031045010H10E1001011044010H101103104401021001011044010210010110:40102100101103301001011044010210010110:401021001011035010?10C10G10010130100101104000040102100101103401021001011035010;1071081001016010;1071081001011037010210;107108100101103401021001011094010210010I10940105100101104401051011031047010210510010110310D10660102105100101103106401051001011065010210510010110350102105100101103501021051001011035010>10F1001011064010=10510010130105100101XN;XF4P2P7O2n200110B00012110@10KXH:P7O1P>n10110A00021110B00bG%j7#2%i2#2[eXA3P7O1WAo"). Qed.
End FRMC.

End FrmKeepC.
Module DrainSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WallSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_DrainSim () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsCeq_rewrite_relationI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes;EquivalenceEpointwise_equivalenceC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:Proper_mapc59OSSVerify5KrLib7Mh_00387CatExec=flat_map_app'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00387CatExec9skipn_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_00387CatExec>flat_map_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00387WallSim:u_len_wordC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib7Mh_00388DrainSim5procsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics?LinuxProcessSem5State5event01c59OSSVerify5KrLib7Mh_00388DrainSim8reads_chC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C45stdpp9bitvector;definitions7Z_to_bvc59OSSVerify5KrLib7Mh_00388DrainSim=reads_ch_consC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib7Mh_00388DrainSim=drain_from_chC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib7Mh_00388DrainSim8out_tailC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00389StreamSim6chunks00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K4ELinuxProcessSemantics?LinuxProcessSem5State5event03I4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00I47Corelib4Init5Logic2or00c59OSSVerify5KrLib7Mh_00388DrainSimDdrain_from_ch_prefixC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00389StreamSim6chunks01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSimAdrain_from_ch_nilC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K4ELinuxProcessSemantics?LinuxProcessSem5State5event02K4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream01c59OSSVerify5KrLib7Mh_00388DrainSimAdrain_from_ch_outC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions;bv_unsignedk59OSSVerify5KrLib7Mh_00389StreamSim6chunks02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim9procs_appC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;stream_takeC47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib7Mh_00388DrainSimCdrain_from_ch_blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rc59OSSVerify5KrLib7Mh_00388DrainSimAdrain_from_ch_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim7fd1chanC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00388DrainSim5to_rd00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01k59OSSVerify5KrLib7Mh_00388DrainSim5to_rd02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:msteps_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib7Mh_00388DrainSim7lh_nextC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00388DrainSim6to_out00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00388DrainSim6to_out03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00307ExitSim7to_exit00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00387WallSim7to_wall10C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387WallSim7to_wall11C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim5WrFinC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00i59OSSVerify5KrLib7Mh_00387WallSim7to_wall00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387WallSim7to_wall12C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00387WallSim7to_wall13C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim:to_out_indC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib7Mh_00388DrainSim<msteps_to_rdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c59OSSVerify5KrLib7Mh_00388DrainSim8ReadPendC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00K4ELinuxProcessSemantics?LinuxProcessSem3Run4star01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepC4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01K4ELinuxProcessSemantics?LinuxProcessSem3Run4star02c59OSSVerify5KrLib7Mh_00388DrainSim9to_rd_indC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_00306CatSim;buf_modeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib7Mh_00307ExitSimCto_exit_star_admitsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib7Mh_00306CatSim>fd1chan_fdchanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSimCto_wall_star_admitsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00c59OSSVerify5KrLib7Mh_00389StreamSim9band0_255C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSim6fd32_1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00307ExitSimAto_exit_star_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSimAto_wall_star_onlyC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00C59OSSVerify5KrLib7Mh_00307ExitSim?sstep_instr_invC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00c59OSSVerify5KrLib7Mh_00389StreamSim?read0_check_eofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim<read0_ok_eofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSimAread0_check_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim>read0_ok_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim<read0_ok_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSimBread0_no_unmodeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim>sstep_read_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim6M_loopC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@ms_writable_byteC4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_mapC4ELinuxProcessSemantics?LinuxProcessSem5State:access_okbC4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC4ELinuxProcessSemantics?LinuxProcessSem5State:with_stdinC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specc59OSSVerify5KrLib7Mh_00388DrainSimBread0_ok_bytes_cntC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesc59OSSVerify5KrLib7Mh_00389StreamSimDm_vm_lazy_with_stdinC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00c59OSSVerify5KrLib7Mh_00388DrainSim5readsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim:to_rd_starC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim@read0_ok_eof_cntC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C59OSSVerify5KrLib7Mh_00306CatSimEapply_effect_no_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSimBto_out_star_admitsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run:star_transK4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream02c59OSSVerify5KrLib7Mh_00389StreamSim;M_loop_takeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim?drain_read_stepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim:reads_consC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indc59OSSVerify5KrLib7Mh_00389StreamSim:chunks_indC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib7Mh_00387SeqExec>land_255_smallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim:drain_fromC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim>drain_from_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSimBsstep_read_inv_cntC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim@to_out_star_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim>drain_from_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim@drain_from_blockC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim>drain_from_errC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run8star_indC59OSSVerify5KrLib7Mh_00306CatSim6fdchanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim4dinvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC59OSSVerify5KrLib7Mh_00307ExitSim7on_pathC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib7Mh_00307ExitSim<on_path_stepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSimAsstep_to_wall_invC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib7Mh_00306CatSimAbuf_modeled_skipnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim@to_out_wall_tailC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSimBwall_out_dinv_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00307ExitSim@on_path_no_errorC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387WallSimFto_wall_no_error_sstepC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02C59OSSVerify5KrLib7Mh_00266SimInv8star_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim9dinv_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00266SimInvDinv_no_reaches_errorC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim=dinv_no_errorC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8in_stdinC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedc59OSSVerify5KrLib7Mh_00389StreamSim;init_M_loopC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelc59OSSVerify5KrLib7Mh_00388DrainSim?star_drain_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSimAdrain_from_prefixC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9obs_tracec59OSSVerify5KrLib7Mh_00388DrainSimDdrain_star_admits_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSim<chunks_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00389StreamSimAchunks_single_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSimEdrain_star_admits_errC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC47Corelib4Init5Logic3iffI47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00c59OSSVerify5KrLib7Mh_00388DrainSim>to_rd_no_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00266SimInv:inv_coexecC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim<to_rd_coexecC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6coexec00K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:omni_corunC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=prefix_closedI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6cosafe00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun>cosafe_obs_iffc59OSSVerify5KrLib7Mh_00388DrainSim=drain_obs_iffC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunGobs_trace_prefix_closedC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;omni_cosafeI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<img_segmentsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7coveredC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence:omni_equivc59OSSVerify5KrLib7Mh_00388DrainSim@drain_omni_corunC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRunDnever_errors_coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=coexec_conseqC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun8omni_runC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence@omni_trace_equivC4ELinuxProcessSemantics?LinuxProcessSem3Run3runC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalenceDtrace_equiv_iff_omniC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes?RelationClasses;reflexivityC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxC4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6errorsI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_Reflexivec59OSSVerify5KrLib7Mh_00388DrainSimGdrain_omni_strong_equivC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence7modeledC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence5equivc59OSSVerify5KrLib7Mh_00388DrainSim>drain_no_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00266SimInvDno_error_run_modeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=bh_all_errorsC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errors".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Proc.
Context {A : Type}.
Variable f : A -> byte -> option A.

Fixpoint procs (a : A) (bs : list byte) : option A :=
  match bs with
  | [] => Some a
  | b :: rest => match f a b with Some a' => procs a' rest | None => None end
  end.

Lemma procs_app : forall bs1 bs2 a,
  procs a (bs1 ++ bs2) =
  match procs a bs1 with Some a' => procs a' bs2 | None => None end.
Proof.
  induction bs1 as [|b bs1 IH]; intros bs2 a; [reflexivity|].
  cbn [procs app]. destruct (f a b); [apply IH | reflexivity].
Qed.
End Proc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition block_ok (cnt : word) (bs : list byte) : Prop :=
  (1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z.

(* [comment removed for export] *)
Definition reads_ch (rch : word) (blocks : list (list byte)) : list event :=
  flat_map (fun bs => map (ReadEv rch) bs) blocks.

Lemma reads_ch_cons : forall rch bs blocks,
  reads_ch rch (bs :: blocks) = map (ReadEv rch) bs ++ reads_ch rch blocks.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition reads (blocks : list (list byte)) : list event :=
  reads_ch (Z_to_bv 64 0) blocks.

Lemma reads_cons : forall bs blocks,
  reads (bs :: blocks) = map (ReadEv (Z_to_bv 64 0)) bs ++ reads blocks.
Proof. exact (reads_ch_cons (Z_to_bv 64 0)). Qed.

Section Traces.
Context {A : Type}.
Variable cnt : word.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.

(* [comment removed for export] *)
Definition out_tail (s : InputStream) (a : A) (fs : Fs.Fs) : list event :=
  match s with
  | IEof => map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]
  | ICons _ _ => []
  end.

(* [comment removed for export] *)
Definition drain_from_ch (rch : word) (a : A) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  (exists blocks s' a',
     chunks cnt s blocks s' /\
     procs f a (concat blocks) = Some a' /\
     is_prefix tr (reads_ch rch blocks ++ out_tail s' a' fs))
  \/ (exists blocks bs s' a',
     chunks cnt s (blocks ++ [bs]) s' /\
     procs f a (concat blocks) = Some a' /\
     procs f a' bs = None /\
     is_prefix tr (reads_ch rch (blocks ++ [bs]) ++ [ExitEv ec fs])).

(* [comment removed for export] *)
Definition drain_from (a : A) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  drain_from_ch (Z_to_bv 64 0) a fs s tr.

Lemma drain_from_ch_prefix : forall rch a fs s tr tr',
  drain_from_ch rch a fs s tr -> is_prefix tr' tr -> drain_from_ch rch a fs s tr'.
Proof.
  intros rch a fs s tr tr' [ (blocks & s' & a' & HC & Hp & Hpref)
                           | (blocks & bs & s' & a' & HC & Hp & Hn & Hpref) ] Hp'.
  - left. exists blocks, s', a'.
    split; [exact HC | split; [exact Hp | eapply is_prefix_trans; eauto]].
  - right. exists blocks, bs, s', a'.
    split; [exact HC | split; [exact Hp |
    split; [exact Hn | eapply is_prefix_trans; eauto]]].
Qed.

Lemma drain_from_prefix : forall a fs s tr tr',
  drain_from a fs s tr -> is_prefix tr' tr -> drain_from a fs s tr'.
Proof. exact (drain_from_ch_prefix (Z_to_bv 64 0)). Qed.

Lemma drain_from_ch_nil : forall rch a fs s, drain_from_ch rch a fs s [].
Proof.
  intros rch a fs s. left. exists [], s, a.
  split; [constructor | split; [reflexivity | apply is_prefix_nil]].
Qed.

Lemma drain_from_nil : forall a fs s, drain_from a fs s [].
Proof. exact (drain_from_ch_nil (Z_to_bv 64 0)). Qed.

(* [comment removed for export] *)
Lemma drain_from_ch_out : forall rch a fs tr,
  is_prefix tr (map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]) ->
  drain_from_ch rch a fs IEof tr.
Proof.
  intros rch a fs tr Hp. left. exists [], IEof, a.
  split; [constructor | split; [reflexivity | exact Hp]].
Qed.

Lemma drain_from_out : forall a fs tr,
  is_prefix tr (map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]) ->
  drain_from a fs IEof tr.
Proof. exact (drain_from_ch_out (Z_to_bv 64 0)). Qed.

Lemma drain_from_ch_block : forall rch a a1 fs s bs tr,
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take s (length bs)) = bs ->
  procs f a bs = Some a1 ->
  drain_from_ch rch a1 fs (snd (stream_take s (length bs))) tr ->
  drain_from_ch rch a fs s (map (ReadEv rch) bs ++ tr).
Proof.
  intros rch a a1 fs s bs tr Hlo Hhi Hpre Hs
    [ (blocks & s' & a' & HC & Hp & Hpref)
    | (blocks & bsE & s' & a' & HC & Hp & Hn & Hpref) ].
  - left. exists (bs :: blocks), s', a'.
    split; [eapply chunks_cons; eassumption |].
    split; [cbn [concat]; rewrite procs_app, Hs; exact Hp |].
    rewrite reads_ch_cons, <- app_assoc.
    apply is_prefix_app_mono. exact Hpref.
  - right. exists (bs :: blocks), bsE, s', a'.
    split; [change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE]));
            eapply chunks_cons; eassumption |].
    split; [cbn [concat]; rewrite procs_app, Hs; exact Hp |].
    split; [exact Hn |].
    change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE])).
    rewrite reads_ch_cons, <- app_assoc.
    apply is_prefix_app_mono. exact Hpref.
Qed.

Lemma drain_from_block : forall a a1 fs s bs tr,
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take s (length bs)) = bs ->
  procs f a bs = Some a1 ->
  drain_from a1 fs (snd (stream_take s (length bs))) tr ->
  drain_from a fs s (map (ReadEv (Z_to_bv 64 0)) bs ++ tr).
Proof. exact (drain_from_ch_block (Z_to_bv 64 0)). Qed.

Lemma drain_from_ch_err : forall rch a fs s bs tr,
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take s (length bs)) = bs ->
  procs f a bs = None ->
  is_prefix tr [ExitEv ec fs] ->
  drain_from_ch rch a fs s (map (ReadEv rch) bs ++ tr).
Proof.
  intros rch a fs s bs tr Hlo Hhi Hpre Hn Hp. right.
  exists [], bs, (snd (stream_take s (length bs))), a.
  split; [cbn [app]; eapply chunks_cons;
          try eassumption; constructor |].
  split; [reflexivity |].
  split; [exact Hn |].
  cbn [app]. unfold reads_ch. cbn [flat_map]. rewrite app_nil_r.
  apply is_prefix_app_mono. exact Hp.
Qed.

Lemma drain_from_err : forall a fs s bs tr,
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take s (length bs)) = bs ->
  procs f a bs = None ->
  is_prefix tr [ExitEv ec fs] ->
  drain_from a fs s (map (ReadEv (Z_to_bv 64 0)) bs ++ tr).
Proof. exact (drain_from_ch_err (Z_to_bv 64 0)). Qed.

End Traces.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd1chan_with_stdin : forall s m, fd1chan m -> fd1chan (with_stdin s m).
Proof. intros s m H. exact H. Qed.

Lemma m_fds_with_stdin : forall s m, m_fds (with_stdin s m) = m_fds m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Drain.
Context {A : Type}.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable cnt : word.
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.
Hypothesis Hec : (bv_unsigned ec < 256)%Z.
Variable LH : A -> machine_state -> Prop.

(* [comment removed for export] *)
Definition lh_next (a : A) (ms : machine_state) : Prop :=
  exists ms', msteps segs ms ms' /\ LH a ms'.

(* [comment removed for export] *)
Definition WrFin (bs : list byte) (ms : machine_state) : Prop :=
  (1 <= length bs)%nat /\
  to_wall segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).

(* [comment removed for export] *)
Inductive to_out : list byte -> machine_state -> Prop :=
| tout_exit : forall ms, to_exit segs (Z_to_bv 64 0) ms -> to_out [] ms
| tout_wr : forall bs ms, WrFin bs ms -> to_out bs ms
| tout_step : forall bs ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_out bs ms' -> to_out bs ms.

(* [comment removed for export] *)
Definition ReadPend (a : A) (ms : machine_state) : Prop :=
  exists buf x8,
  ms_svc_pending ms = Some x8 /\
  bv_unsigned x8 = 63%Z /\
  ms_gpr ms 0 = Z_to_bv 64 0 /\
  ms_gpr ms 1 = buf /\
  ms_gpr ms 2 = cnt /\
  (exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt
             = Some w) /\
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true /\
  to_out (out a) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
  (* [comment removed for export] *)
  buf_modeled (out a) /\
  (forall bs,
     (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
     match procs f a bs with
     | Some a' => lh_next a'
         (advance_past_svc (apply_effect ms
            (mkEffect (len_word bs) [(buf, bs)] [])))
     | None => to_exit segs ec
         (advance_past_svc (apply_effect ms
            (mkEffect (len_word bs) [(buf, bs)] [])))
     end).

(* [comment removed for export] *)
Inductive to_rd : A -> machine_state -> Prop :=
| trd_here : forall a ms, ReadPend a ms -> to_rd a ms
| trd_step : forall a ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd a ms' -> to_rd a ms.

Lemma msteps_to_rd : forall a ms ms',
  msteps segs ms ms' -> to_rd a ms' -> to_rd a ms.
Proof.
  intros a ms ms' H; induction H; [auto|].
  intro Hrd. eapply trd_step; eauto.
Qed.

Lemma msteps_to_out : forall bs ms ms',
  msteps segs ms ms' -> to_out bs ms' -> to_out bs ms.
Proof.
  intros bs ms ms' H; induction H; [auto|].
  intro Ho. eapply tout_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma to_out_wall_tail : forall bs ms,
  to_out bs ms ->
  to_wall_tail segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).
Proof.
  intros bs ms H;
    induction H as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH].
  - apply twt_done. exact Hte.
  - destruct HWF as [Hnb Hwl]. apply twt_more; assumption.
  - eapply twt_step; eauto.
Qed.

(* [comment removed for export] *)
Variable H_LH : forall a ms, LH a ms -> to_rd a ms.

Lemma lh_next_to_rd : forall a ms, lh_next a ms -> to_rd a ms.
Proof.
  intros a ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_rd_star : forall a ms model,
  m_halted model = None -> m_vm_lazy model = [] -> to_rd a ms ->
  exists msR, ReadPend a msR /\
    star segs (mkCfg ms model) [] (mkCfg msR model).
Proof.
  intros a ms model Hh Hlazy Hrd.
  induction Hrd as [a ms HRP | a ms ms' Hsvc Hstep Hrd IH].
  - exists ms. split; [exact HRP | apply star_refl].
  - destruct IH as (msR & HRP & Hstar).
    exists msR. split; [exact HRP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma msteps_star : forall ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  star segs (mkCfg ms model) [] (mkCfg ms' model).
Proof.
  intros ms ms' model Hh Hlazy H. induction H as [ms | ms ms1 ms2 Hsvc Hstep H IH].
  - apply star_refl.
  - change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms1 model) | exact IH];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_out_star_admits : forall bs ms model,
  fd1chan model -> m_halted model = None -> m_vm_lazy model = [] ->
  to_out bs ms -> buf_modeled bs ->
  exists c, star segs (mkCfg ms model)
              (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]) c.
Proof.
  intros bs ms model Hfd1 Hh Hlazy Ho Hbm. revert Hbm.
  induction Ho as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH]; intro Hbm.
  - cbn [map app].
    destruct (to_exit_star_admits segs (Z_to_bv 64 0) ms model Hh Hlazy Hte) as [c Hstar].
    exists c. rewrite band0_255 in Hstar. exact Hstar.
  - destruct HWF as (Hnb & Hwl).
    eapply (to_wall_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
              ms bs _ Hwl Hbm model);
      [exact Hh | exact Hlazy | apply fd1chan_fdchan; exact Hfd1 |].
    intros ms' Hex.
    destruct (to_exit_star_admits segs (Z_to_bv 64 0) ms' model Hh Hlazy Hex)
      as [c Hstar].
    exists c. rewrite band0_255 in Hstar. exact Hstar.
  - destruct (IH Hbm) as [c Hstar]. exists c.
    replace (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])
      with ([] ++ (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]))
      by reflexivity.
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_out_star_only : forall bs ms model,
  fd1chan model -> m_halted model = None -> m_vm_lazy model = [] ->
  to_out bs ms -> buf_modeled bs ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]).
Proof.
  intros bs ms model Hfd1 Hh Hlazy Ho Hbm. revert Hbm.
  induction Ho as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH];
    intros Hbm tr c Hstar.
  - cbn [map app].
    destruct (to_exit_star_only segs (Z_to_bv 64 0) ms model Hh Hlazy Hte tr c Hstar)
      as [-> | ->].
    + apply is_prefix_nil.
    + rewrite band0_255. apply is_prefix_refl.
  - destruct HWF as (Hnb & Hwl).
    eapply (to_wall_star_only segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
              ms bs _ Hwl Hbm model);
      [exact Hh | exact Hlazy | apply fd1chan_fdchan; exact Hfd1 | | exact Hstar].
    intros ms' tr' c' Hex Hstar'.
    destruct (to_exit_star_only segs (Z_to_bv 64 0) ms' model Hh Hlazy Hex tr' c' Hstar')
      as [-> | ->].
    + apply is_prefix_nil.
    + rewrite band0_255. apply is_prefix_refl.
  - inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst; [apply is_prefix_nil|].
    destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
    subst evs. inversion Hc2; subst c2. cbn [app].
    exact (IH Hbm tr2 _ Hstar2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read0_check_eof_cnt : forall ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  m_stdin model = IEof ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  check_read (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (mkEffect (Z_to_bv 64 0) [] []) model
    = CheckOk model [].
Proof. apply (StreamSim.read0_check_eof cnt Hcnt). Qed.

Lemma read0_ok_eof_cnt : forall ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  m_stdin model = IEof ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (Z_to_bv 64 0) [] []) model []).
Proof. apply (StreamSim.read0_ok_eof cnt Hcnt). Qed.

Lemma read0_check_bytes_cnt : forall ms x8 model w bs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  check_read (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model
    = CheckOk (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
              (map (ReadEv (Z_to_bv 64 0)) bs).
Proof. apply (StreamSim.read0_check_bytes cnt Hcnt). Qed.

Lemma read0_ok_bytes_cnt : forall ms x8 model w bs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
        (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
        (map (ReadEv (Z_to_bv 64 0)) bs)).
Proof. apply (StreamSim.read0_ok_bytes cnt Hcnt). Qed.

Lemma read0_ok_inv_cnt : forall ms x8 model buf w eff model' evs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  (m_stdin model = IEof /\ eff = mkEffect (Z_to_bv 64 0) [] [] /\
   model' = model /\ evs = [])
  \/ (exists bs,
        (1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
        fst (stream_take (m_stdin model) (length bs)) = bs /\
        eff = mkEffect (len_word bs) [(buf, bs)] [] /\
        model' = with_stdin (snd (stream_take (m_stdin model) (length bs))) model /\
        evs = map (ReadEv (Z_to_bv 64 0)) bs).
Proof. apply (StreamSim.read0_ok_inv cnt Hcnt). Qed.

Lemma read0_no_err_cnt : forall ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof. apply (StreamSim.read0_no_unmodeled cnt Hcnt). Qed.

Lemma sstep_read_inv_cnt : forall ms model buf x8 w evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true ->
  sstep segs (mkCfg ms model) evs st ->
  (m_stdin model = IEof /\ evs = [] /\
   st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model))
  \/ (exists bs,
        (1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
        fst (stream_take (m_stdin model) (length bs)) = bs /\
        evs = map (ReadEv (Z_to_bv 64 0)) bs /\
        st = SNext (mkCfg
               (advance_past_svc (apply_effect ms
                  (mkEffect (len_word bs) [(buf, bs)] [])))
               (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                           model))).
Proof. apply (StreamSim.sstep_read_inv cnt Hcnt). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma drain_read_step : forall bs ms model buf x8 w,
  M_loop model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf ->
  ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  access_okb buf (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  sstep segs (mkCfg ms model) (map (ReadEv (Z_to_bv 64 0)) bs)
    (SNext (mkCfg (advance_past_svc (apply_effect ms
                     (mkEffect (len_word bs) [(buf, bs)] [])))
                  (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                              model))).
Proof.
  intros bs ms model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hlo Hhi Hpre.
  pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  apply (sstep_syscall segs ms model x8
           (mkEffect (len_word bs) [(buf, bs)] [])
           (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
           (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
           (map (ReadEv (Z_to_bv 64 0)) bs));
    [exact Hh | exact Hsvc | | exact Hh |].
  - rewrite <- Hg1. rewrite <- Hg1 in Hw, Haok.
    apply read0_ok_bytes_cnt with (w := w); assumption.
  - rewrite (materialize_model_accesses_no_lazy _ _).
    + reflexivity.
    + rewrite m_vm_lazy_with_stdin. exact Hlazy.
Qed.

Lemma drain_star_admits_ok : forall s blocks s',
  chunks cnt s blocks s' ->
  forall a a' ms model,
  M_loop model -> m_stdin model = s -> to_rd a ms ->
  procs f a (concat blocks) = Some a' ->
  exists c, star segs (mkCfg ms model)
              (reads blocks ++ out_tail out s' a' (m_fs model)) c.
Proof.
  intros s blocks s' HC.
  induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros a a' ms model HM Hst Hrd Hp;
    pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  - cbn [concat procs] in Hp. injection Hp as <-.
    unfold reads, reads_ch. cbn [flat_map app].
    destruct s as [|b0 s0] eqn:Hs.
    + (* the input has run out: EOF read, then the finishing phase *)
      destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
      destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & _).
      assert (HssE : sstep segs (mkCfg msR model) []
                (SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0)))
                              model))).
      { rewrite <- (apply_effect_no_write msR (Z_to_bv 64 0)).
        apply (sstep_syscall segs msR model x8 (mkEffect (Z_to_bv 64 0) [] [])
                 model model []);
          [exact Hh | exact Hsvc | | exact Hh |].
        - rewrite <- Hg1 in Hw, Haok.
          exact (read0_ok_eof_cnt msR x8 model w Hno Hfd0 Hst Hg0 Hg2 Hw
                   Haok).
        - rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity. }
      destruct (to_out_star_admits (out a) _ model Hfd1 Hh Hlazy Hout Hobm) as [c Hstar2].
      exists c. cbn [out_tail].
      replace (map (WriteEv (Z_to_bv 64 1)) (out a)
                 ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])
        with (([] : list event)
                ++ ([] ++ (map (WriteEv (Z_to_bv 64 1)) (out a)
                             ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])))
        by reflexivity.
      eapply star_trans; [exact Hstar0|].
      eapply star_step; [exact HssE | exact Hstar2].
    + (* input remains: nothing more is emitted along this chunking *)
      cbn [out_tail app]. exists (mkCfg ms model). apply star_refl.
  - (* one more block *)
    cbn [concat] in Hp. rewrite procs_app in Hp.
    destruct (procs f a bs) as [a1|] eqn:Hp1; [|discriminate].
    destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
    pose proof (Hbytes bs Hlo Hhi) as Hcont.
    rewrite Hp1 in Hcont.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bs) [(buf, bs)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bs))) model).
    assert (HM' : M_loop model')
      by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
    assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
      by reflexivity.
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
              (SNext (mkCfg advB model'))).
    { unfold advB, model'. rewrite <- Hst.
      eapply (drain_read_step bs msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
                Hlo Hhi); rewrite Hst; exact Hpre. }
    destruct Hcont as (msL & Hms & HLa1).
    pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
    destruct (IH a1 a' advB model' HM' Hst' Hrd1 Hp) as [c Hstar3].
    exists c.
    change (m_fs model') with (m_fs model) in Hstar3.
    rewrite reads_cons, <- app_assoc.
    replace (map (ReadEv (Z_to_bv 64 0)) bs
               ++ reads blocks ++ out_tail out s'' a' (m_fs model))
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bs
                    ++ (reads blocks ++ out_tail out s'' a' (m_fs model))))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar3].
Qed.

Lemma drain_star_admits_err : forall s blocks s1,
  chunks cnt s blocks s1 ->
  forall a a' bsE ms model,
  M_loop model -> m_stdin model = s -> to_rd a ms ->
  procs f a (concat blocks) = Some a' ->
  (1 <= Z.of_nat (length bsE))%Z -> (Z.of_nat (length bsE) <= bv_unsigned cnt)%Z ->
  fst (stream_take s1 (length bsE)) = bsE ->
  procs f a' bsE = None ->
  exists c, star segs (mkCfg ms model)
              (reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)]) c.
Proof.
  intros s blocks s1 HC.
  induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros a a' bsE ms model HM Hst Hrd Hp HloE HhiE HpreE Hn;
    pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  - cbn [concat procs] in Hp. injection Hp as <-.
    destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
    pose proof (Hbytes bsE HloE HhiE) as Hcont.
    rewrite Hn in Hcont.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bsE) [(buf, bsE)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bsE))) model).
    assert (Hh' : m_halted model' = None) by exact Hh.
    assert (Hlazy' : m_vm_lazy model' = [])
      by (unfold model'; rewrite m_vm_lazy_with_stdin; exact Hlazy).
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bsE)
              (SNext (mkCfg advB model'))).
    { unfold advB, model'. rewrite <- Hst.
      eapply (drain_read_step bsE msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
                HloE HhiE); rewrite Hst; exact HpreE. }
    destruct (to_exit_star_admits segs ec advB model' Hh' Hlazy' Hcont) as [c Hstar2].
    rewrite land_255_small in Hstar2 by exact Hec.
    change (m_fs model') with (m_fs model) in Hstar2.
    exists c.
    cbn [app]. unfold reads, reads_ch. cbn [flat_map]. rewrite app_nil_r.
    replace (map (ReadEv (Z_to_bv 64 0)) bsE ++ [ExitEv ec (m_fs model)])
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bsE ++ [ExitEv ec (m_fs model)]))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar2].
  - cbn [concat] in Hp. rewrite procs_app in Hp.
    destruct (procs f a bs) as [a1|] eqn:Hp1; [|discriminate].
    destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
    pose proof (Hbytes bs Hlo Hhi) as Hcont.
    rewrite Hp1 in Hcont.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bs) [(buf, bs)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bs))) model).
    assert (HM' : M_loop model')
      by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
    assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
      by reflexivity.
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
              (SNext (mkCfg advB model'))).
    { unfold advB, model'. rewrite <- Hst.
      eapply (drain_read_step bs msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
                Hlo Hhi); rewrite Hst; exact Hpre. }
    destruct Hcont as (msL & Hms & HLa1).
    pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
    destruct (IH a1 a' bsE advB model' HM' Hst' Hrd1 Hp HloE HhiE HpreE Hn)
      as [c Hstar3].
    exists c.
    change (m_fs model') with (m_fs model) in Hstar3.
    change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE])).
    rewrite reads_cons, <- app_assoc.
    replace (map (ReadEv (Z_to_bv 64 0)) bs
               ++ reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)])
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bs
                    ++ (reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)])))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma star_drain_only : forall c0 tr c', star segs c0 tr c' ->
  forall a ms model, c0 = mkCfg ms model -> M_loop model -> to_rd a ms ->
  drain_from cnt f out ec a (m_fs model) (m_stdin model) tr.
Proof.
  intros c0 tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH];
    intros a ms model Heq HM Hrd; subst.
  - apply drain_from_nil.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms' Hsvc Hstep Hrd'].
    + (* at the read ecall *)
      destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
      destruct (sstep_read_inv_cnt ms model buf x8 w evs (SNext c2)
                  Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
        as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
        inversion Hc2; subst.
      * (* end of input: the rest is the finishing phase *)
        pose proof (to_out_star_only (out a) _ model Hfd1 Hh Hlazy Hout Hobm
                      tr2 c3 Hstar) as Hpref.
        cbn [app]. rewrite Hs. apply drain_from_out. exact Hpref.
      * (* bytes *)
        pose proof (Hbytes bs Hlo Hhi) as Hcont.
        destruct (procs f a bs) as [a1|] eqn:Hp1.
        -- destruct Hcont as (msL & Hms & HLa1).
           pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
           apply drain_from_block with (a1 := a1);
             [exact Hlo | exact Hhi | exact Hpre | exact Hp1 |].
           exact (IH a1 _ _ eq_refl (M_loop_take (length bs) model HM) Hrd1).
        -- apply drain_from_err;
             [exact Hlo | exact Hhi | exact Hpre | exact Hp1 |].
           destruct (to_exit_star_only segs ec _
                       (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                                   model) Hh ltac:(rewrite m_vm_lazy_with_stdin; exact Hlazy)
                       Hcont tr2 c3 Hstar)
             as [-> | ->].
           ++ apply is_prefix_nil.
           ++ change (m_fs (with_stdin
                              (snd (stream_take (m_stdin model) (length bs)))
                              model)) with (m_fs model).
              rewrite land_255_small by exact Hec. apply is_prefix_refl.
    + (* an ordinary instruction *)
      destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                  Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
      subst evs. inversion Hc2; subst c2. cbn [app].
      exact (IH a _ model eq_refl HM Hrd').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dinv (c : config) : Prop :=
  (M_loop (cfg_model c) /\ exists a, to_rd a (cfg_ms c))
  \/ (fd1chan (cfg_model c) /\ m_halted (cfg_model c) = None /\
      m_vm_lazy (cfg_model c) = [] /\
      exists rest, buf_modeled rest /\
        to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) rest
          (to_exit segs (Z_to_bv 64 0)))
  \/ on_path segs (Z_to_bv 64 0) c
  \/ on_path segs ec c.

Lemma wall_out_dinv_step : forall rest ms model evs ms' model',
  fd1chan model -> m_halted model = None -> m_vm_lazy model = [] ->
  buf_modeled rest ->
  to_wall_tail segs (Z_to_bv 64 1) ms rest (to_exit segs (Z_to_bv 64 0)) ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg ms' model')) ->
  dinv (mkCfg ms' model').
Proof.
  intros rest ms model evs ms' model' Hfd1 Hh Hlazy Hbm Ht Hss.
  assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
    by (apply fd1chan_fdchan; exact Hfd1).
  revert Hbm.
  inversion Ht as [msD kD HkD | msM restM kM HnbM Hwl
                  | msS msS' restS kS HsvcS HstepS Ht']; subst; intro Hbm.
  - (* twt_done: on the exit line *)
    right. right. left.
    apply (on_path_step segs (Z_to_bv 64 0) (mkCfg ms model) evs); [|exact Hss].
    left. repeat split; assumption.
  - (* twt_more: at the write ecall *)
    destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                ms rest _ model evs (SNext (mkCfg ms' model'))
                Hh Hlazy Hfdc Hbm Hwl Hss) as (n & Hn1 & Hn2 & _ & Hc2 & Ht2).
    inversion Hc2; subst.
    right. left. cbn. split; [exact Hfd1 | repeat split; try assumption].
    exists (skipn n rest).
    split; [apply buf_modeled_skipn; exact Hbm | exact Ht2].
  - (* twt_step *)
    destruct (sstep_instr_inv segs ms model msS' evs (SNext (mkCfg ms' model'))
                Hlazy HsvcS HstepS Hss) as [_ Hc2].
    inversion Hc2; subst.
    right. left. cbn. split; [exact Hfd1 | repeat split; try assumption].
    exists rest. split; [exact Hbm | exact Ht'].
Qed.
Lemma dinv_step : forall c evs c',
  dinv c -> sstep segs c evs (SNext c') -> dinv c'.
Proof.
  intros [ms model] evs [ms' model'] Hinv Hss.
  destruct Hinv as
    [[HM (a & Hrd)] | [[Hfd1 [Hh [Hlazy (rest & Hbm & Ht)]]] | [Hop | Hop]]];
    cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms1 Hsvc Hstep Hrd'].
    + destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
      destruct (sstep_read_inv_cnt ms model buf x8 w evs
                  (SNext (mkCfg ms' model'))
                  Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
        as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
        inversion Hc2; subst.
      * right. left. cbn. split; [exact Hfd1 | repeat split; try assumption].
        exists (out a).
        split; [exact Hobm | exact (to_out_wall_tail _ _ Hout)].
      * pose proof (Hbytes bs Hlo Hhi) as Hcont.
        destruct (procs f a bs) as [a1|] eqn:Hp1.
        -- destruct Hcont as (msL & Hms & HLa1).
           left. cbn. split; [apply M_loop_take; exact HM|].
           exists a1. exact (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)).
        -- right. right. right. left. cbn. split; [exact Hh|].
           split; [exact Hlazy | exact Hcont].
    + destruct (sstep_instr_inv segs ms model ms1 evs
                  (SNext (mkCfg ms' model')) Hlazy Hsvc Hstep Hss) as [_ Hc2].
      inversion Hc2; subst.
      left. cbn. split; [exact HM |]. exists a. exact Hrd'.
  - exact (wall_out_dinv_step rest ms model evs ms' model' Hfd1 Hh Hlazy Hbm Ht Hss).
  - right. right. left. eapply on_path_step; eauto.
  - right. right. right. eapply on_path_step; eauto.
Qed.

Lemma dinv_no_error : forall c evs, dinv c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hinv Hss.
  destruct Hinv as
    [[HM (a & Hrd)] | [[Hfd1 [Hh [Hlazy (rest & Hbm & Ht)]]] | [Hop | Hop]]];
    cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms1 Hsvc Hstep Hrd'].
    + destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
      destruct (sstep_read_inv_cnt ms model buf x8 w evs SError
                  Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
        as [(_ & _ & Hc2) | (bs & _ & _ & _ & _ & Hc2)]; discriminate.
    + destruct (sstep_instr_inv segs ms model ms1 evs SError
                  Hlazy Hsvc Hstep Hss) as [_ Hc2]. discriminate.
  - assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    inversion Ht as [msD kD HkD | msM restM kM HnbM Hwl
                    | msS msS' restS kS HsvcS HstepS Ht']; subst.
    + eapply (on_path_no_error segs (Z_to_bv 64 0) (mkCfg ms model));
        [left; repeat split; assumption | exact Hss].
    + exact (to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               ms rest _ model evs Hh Hlazy Hfdc Hbm Hwl Hss).
    + destruct (sstep_instr_inv segs ms model msS' evs SError
                  Hlazy HsvcS HstepS Hss) as [_ Hc2]. discriminate.
  - eapply on_path_no_error; eauto.
  - eapply on_path_no_error; eauto.
Qed.

Lemma star_dinv : forall c tr c', dinv c -> star segs c tr c' -> dinv c'.
Proof. exact (star_inv segs dinv dinv_step). Qed.

Lemma to_rd_no_error : forall a ms model,
  M_loop model -> to_rd a ms -> ~ reaches_error segs (mkCfg ms model).
Proof.
  intros a ms model HM Hrd.
  apply (inv_no_reaches_error segs dinv dinv_step dinv_no_error).
  left; cbn; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma drain_obs_iff : forall pc ph sp brk0 mb rnd lim inp a0,
  to_rd a0 (init_machine_state segs pc ph sp mb rnd inp) ->
  in_channel_reader inp = true ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> drain_from cnt f out ec a0 (in_fs inp) (in_stdin inp) tr.
Proof.
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd Hrdr tr.
  set (fs0 := in_fs inp) in *; set (stdin0 := in_stdin inp) in *.
  unfold init_config.
  set (ms0 := init_machine_state segs pc ph sp mb rnd inp) in *.
  pose proof (init_M_loop (segments_reserved segs) brk0 mb sp lim inp Hrdr) as HM0'.
  set (model0 := with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                   (init_model (segments_reserved segs) brk0 mb sp lim inp)) in *.
  assert (HM0 : StreamSim.M_loop model0) by exact HM0'.
  assert (Hst0 : m_stdin model0 = stdin0) by reflexivity.
  assert (Hfs0 : m_fs model0 = fs0) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    pose proof (star_drain_only _ _ _ Hstar a0 ms0 model0 eq_refl HM0 Hrd) as Hd.
    rewrite Hst0, Hfs0 in Hd.
    eapply drain_from_prefix; eauto.
  - intros [ (blocks & s' & a' & HC & Hp & Hpref)
           | (blocks & bsE & s' & a' & HC & Hp & Hn & Hpref) ].
    + destruct (drain_star_admits_ok _ blocks s' HC a0 a' ms0 model0
                  HM0 Hst0 Hrd Hp) as [c Hstar].
      rewrite Hfs0 in Hstar.
      eexists; exists c; split; [exact Hstar | exact Hpref].
    + destruct (chunks_split _ blocks [bsE] _ _ HC) as (s1 & HC1 & HC2).
      destruct (chunks_single_inv _ _ _ _ HC2) as (HloE & HhiE & HpreE & _).
      destruct (drain_star_admits_err _ blocks s1 HC1 a0 a' bsE ms0 model0
                  HM0 Hst0 Hrd Hp HloE HhiE HpreE Hn) as [c Hstar].
      rewrite Hfs0 in Hstar.
      eexists; exists c; split; [exact Hstar | exact Hpref].
Qed.

Lemma drain_no_error : forall pc ph sp brk0 mb rnd lim inp a0,
  to_rd a0 (init_machine_state segs pc ph sp mb rnd inp) ->
  in_channel_reader inp = true ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd Hrdr.
  apply (to_rd_no_error a0); [apply init_M_loop; exact Hrdr | exact Hrd].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_rd_coexec : forall a ms model,
  M_loop model -> to_rd a ms -> OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof.
  intros a ms model HM Hrd.
  apply (inv_coexec segs dinv dinv_step dinv_no_error).
  left; cbn. split; [exact HM | exists a; exact Hrd].
Qed.

Lemma drain_omni_corun : forall pc ph sp brk0 mb rnd lim inp a0,
  to_rd a0 (init_machine_state segs pc ph sp mb rnd inp) ->
  in_channel_reader inp = true ->
  OmniRun.coexec segs (init_config segs pc ph sp brk0 mb rnd lim inp) never_errors.
Proof.
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd Hrdr. unfold init_config.
  set (model0 := with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                   (init_model (segments_reserved segs) brk0 mb sp lim inp)) in *.
  assert (HM0 : StreamSim.M_loop model0)
    by exact (init_M_loop (segments_reserved segs) brk0 mb sp lim inp Hrdr).
  apply (to_rd_coexec a0); [exact HM0 | exact Hrd].
Qed.

Lemma drain_omni_cosafe : forall pc ph sp brk0 mb rnd lim inp a0,
  to_rd a0 (init_machine_state segs pc ph sp mb rnd inp) ->
  in_channel_reader inp = true ->
  OmniRun.cosafe segs (init_config segs pc ph sp brk0 mb rnd lim inp)
    (drain_from cnt f out ec a0 (in_fs inp) (in_stdin inp)).
Proof.
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd Hrdr.
  apply cosafe_obs_iff.
  - (* prefix-closed, through the trace-set characterisation itself *)
    intros t t' Ht Hp.
    apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd Hrdr).
    eapply obs_trace_prefix_closed; [| exact Hp].
    apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd Hrdr). exact Ht.
  - intros tr Hobs. apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd Hrdr). exact Hobs.
Qed.

End Drain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma drain_omni_strong_equiv :
  forall (A : Type) (cnt : word) (f : A -> byte -> option A)
         (out : A -> list byte) (ec : word) (a0 : A)
         source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd inp,
  (bv_unsigned ec < 256)%Z ->
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  (forall a ms, rLH a ms -> to_rd (run_segments source_segs inp rsp rmb) cnt f out ec rLH a ms) ->
  (forall a ms, aLH a ms -> to_rd (run_segments target_segs inp asp amb) cnt f out ec aLH a ms) ->
  to_rd (run_segments source_segs inp rsp rmb) cnt f out ec rLH a0
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) ->
  to_rd (run_segments target_segs inp asp amb) cnt f out ec aLH a0
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) ->
  in_channel_reader inp = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros A cnt f out ec a0 source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd
         inp Hec Hcnt HrLH HaLH Hr Ha Hrdr.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [exact (drain_omni_corun (run_segments source_segs inp rsp rmb) cnt Hcnt f out ec rLH HrLH
                rpc rph rsp rbrk rmb rrnd source_alloc_limit inp a0 Hr Hrdr) | apply never_errors_covered]. }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (drain_obs_iff (run_segments source_segs inp rsp rmb) cnt Hcnt f out ec Hec rLH HrLH
               rpc rph rsp rbrk rmb rrnd source_alloc_limit inp a0 Hr Hrdr tr).
    rewrite (drain_obs_iff (run_segments target_segs inp asp amb) cnt Hcnt f out ec Hec aLH HaLH
               apc aph asp abrk amb arnd target_alloc_limit inp a0 Ha Hrdr tr).
    reflexivity.
  - exact (drain_omni_corun (run_segments target_segs inp asp amb) cnt Hcnt f out ec aLH HaLH
             apc aph asp abrk amb arnd target_alloc_limit inp a0 Ha Hrdr).
Qed.

Lemma drain_strong_equiv :
  forall (A : Type) (cnt : word) (f : A -> byte -> option A)
         (out : A -> list byte) (ec : word) (a0 : A)
         source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim inp,
  (bv_unsigned ec < 256)%Z ->
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  (forall a ms, rLH a ms -> to_rd (run_segments source_segs inp rsp rmb) cnt f out ec rLH a ms) ->
  (forall a ms, aLH a ms -> to_rd (run_segments target_segs inp asp amb) cnt f out ec aLH a ms) ->
  to_rd (run_segments source_segs inp rsp rmb) cnt f out ec rLH a0
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) ->
  to_rd (run_segments target_segs inp asp amb) cnt f out ec aLH a0
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) ->
  in_channel_reader inp = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros A cnt f out ec a0 source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim
         inp Hec Hcnt HrLH HaLH Hr Ha Hrdr.
  split.
  { apply no_error_run_modeled.
    apply (drain_no_error (run_segments source_segs inp rsp rmb) cnt Hcnt f out ec rLH HrLH
             rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr Hrdr). }
  right. split.
  - intro tr. cbn.
    rewrite (drain_obs_iff (run_segments source_segs inp rsp rmb) cnt Hcnt f out ec Hec rLH HrLH
               rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr Hrdr tr).
    rewrite (drain_obs_iff (run_segments target_segs inp asp amb) cnt Hcnt f out ec Hec aLH HaLH
               apc aph asp abrk amb arnd alim inp a0 Ha Hrdr tr).
    reflexivity.
  - cbn.
    apply (drain_no_error (run_segments target_segs inp asp amb) cnt Hcnt f out ec aLH HaLH
             apc aph asp abrk amb arnd alim inp a0 Ha Hrdr).
Qed.

End DrainSim.
From Stdlib Require ZArith List Lia Bool. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
Module StepTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WallSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.DrainSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_StepTac () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsCeq_rewrite_relationI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes;EquivalenceEpointwise_equivalenceC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:Proper_mapc59OSSVerify5KrLib7Mh_00387CatExec=flat_map_app'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00387CatExec9skipn_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_00387CatExec>flat_map_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00387WallSim:u_len_wordC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordc59OSSVerify5KrLib7Mh_00388DrainSim5procsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim8out_tailC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim7lh_nextC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSimGdrain_omni_strong_equivC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSimBdrain_strong_equivC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7bv_wrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z4of_NK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01c59OSSVerify5KrLib7Mh_00387SeqExec8v_addi_mC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic3notC45stdpp9bitvector;definitions5bv_eqI47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00C49OSSVerify5KrLib8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K46Stdlib9micromega5Tauto8GFormula05C45stdpp9bitvector;definitions=bv_wrap_smallc59OSSVerify5KrLib7Mh_00387StepTac7u_zext8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqc59OSSVerify5KrLib7Mh_00387StepTac>byte_neq_lit_uC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4c_eqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordI47Corelib4Init9Datatypes3nat00C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitionsCbv_wrap_add_idemp_rC45stdpp9bitvector;definitions?bv_add_unsignedC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387StepTac<word_add_natC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega6VarMap1t03C35stdpp7tactics<f_equal_helpC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums1Z03C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addI47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3oppC49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC49OSSVerify5KrLib8PropExecMbuild_stack_bytes_within_spanC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_spanC4ELinuxProcessSemantics?LinuxProcessSem3RunFentry_stack_span_boundK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C4ELinuxProcessSemantics?LinuxProcessSem3RunDentry_stack_span_maxK46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeC56Stdlib6ZArith6BinInt1Z3ltbC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool:orb_true_rC46Stdlib4Bool4Bool<andb_false_rC46Stdlib5Lists4List7forallbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDrange_avoids_ro_segsI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List2Inc59OSSVerify5KrLib7Mh_00387StepTac=ro_segs_belowC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z3lebC47Corelib7Classes9MorphismsDiff_impl_subrelationC56Stdlib6ZArith6BinInt1Z6leb_leC46Stdlib4Bool4Bool=negb_true_iffI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init5Logic2or02C47Corelib7Classes9MorphismsIiff_flip_impl_subrelation".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP1.
Ltac chain_step :=
  first [ eapply mst_step
        | eapply tw_step
        | eapply twm_step
        | eapply MmapSim.twmt_step
        | eapply tmw_step
        | eapply StreamSim.twr_step
        | eapply StreamSim.trd_step
        | eapply WallSim.twt_step
        | eapply WallSim.twe_step
        | eapply DrainSim.tout_step
        | eapply DrainSim.trd_step
        | eapply te_step ].

Section WithFP2.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP2.
Ltac step_intro := chain_step.

Section WithFP3.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP3.
Ltac expand_ctx_defs p :=
  match goal with
  | H := _ |- _ =>
      lazymatch p with
      | context [H] => let p' := eval unfold H in p in expand_ctx_defs p'
      end
  | _ => p
  end.

Section WithFP4.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP4.
Ltac check_closed_term p :=
  let p' := expand_ctx_defs p in
  tryif has_evar p' then
    fail 0 "check_closed_term:" p "contains an evar"
  else tryif match goal with
             | H : _ |- _ => lazymatch p' with context [H] => idtac end
             end
  then fail 0 "check_closed_term:" p "mentions a context variable"
  else idtac.

Section WithFP5.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP5.
Ltac vm_eval t :=
  let _ := match goal with _ => check_closed_term t end in
  eval vm_compute in t.

Section WithFP6.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP6.
Ltac word_lit p :=
  let u := vm_eval (bv_unsigned p) in
  constr:(@BV 64 u ltac:(vm_compute; exact I)).

Section WithFP7.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP7.
Ltac wlit_replace p :=
  let l := word_lit p in
  replace p with l by (apply bv_eq; vm_compute; reflexivity).

Section WithFP8.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP8.
Ltac wlit p :=
  try (lazymatch p with
       | @BV _ _ _ => idtac
       | _ => wlit_replace p
       end).

Section WithFP9.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP9.
Ltac wlits :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_replace (v_addi a b)
  | |- context [btgt ?a ?b] => wlit_replace (btgt a b)
  | |- context [v_jalr ?a ?b] => wlit_replace (v_jalr a b)
  | |- context [v_auipc ?a ?b] => wlit_replace (v_auipc a b)
  end.

Section WithFP10.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP10.
Ltac norm_pc_state st :=
  tryif has_evar st then idtac
  else lazymatch st with
       | mkst _ ?p _ _ => wlit p
       | _ => idtac
       end.
Ltac norm_pc :=
  try lazymatch goal with
  | |- msteps _ ?st _ => norm_pc_state st
  | |- to_wexit _ ?st _ _ => norm_pc_state st
  | |- twm _ ?st _ _ _ => norm_pc_state st
  | |- MmapSim.twm_pend _ ?st _ _ _ _ => norm_pc_state st
  | |- MmapSim.twm_tail _ ?st _ _ _ _ => norm_pc_state st
  | |- tmw _ ?st _ _ _ _ _ => norm_pc_state st
  | |- StreamSim.to_wr _ _ _ ?st => norm_pc_state st
  | |- StreamSim.to_rd _ _ _ ?st => norm_pc_state st
  | |- WallSim.to_wall _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wall_tail _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wallexit _ _ _ _ ?st => norm_pc_state st
  | |- to_exit _ _ ?st => norm_pc_state st
  | |- DrainSim.to_out _ _ ?st => norm_pc_state st
  | |- DrainSim.to_rd _ _ _ _ _ _ _ ?st => norm_pc_state st
  end.

Section WithFP12.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP12.
Ltac reduce_bv_eqb_ifs :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?x else ?y] =>
      lazymatch a with
      | @BV _ _ _ =>
          lazymatch b with
          | @BV _ _ _ =>
              let v := eval vm_compute in (bv_eqb a b) in
              lazymatch v with
              | true => change (if bv_eqb a b then x else y) with x
              | false => change (if bv_eqb a b then x else y) with y
              end
          end
      end
  end.

Section WithFP13.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP13.
Ltac step_simpl := reduce_bv_eqb_ifs; rewrite ?skipn_O; norm_pc.

Section WithFP14.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP14.
Ltac stepi_search F D :=
  first
    [ exact (step_addi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sub _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_auipc _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_andi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sltiu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_xori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)
    (* [comment removed for export] *)
    | exact (step_slti _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srai _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_and _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_xor _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sll _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srl _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sra _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slt _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sltu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_addw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sllw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srlw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sraw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sraiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulh _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulhsu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulhu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_div _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_rem _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_divw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_divuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_remw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_remuw _ _ _ _ _ _ _ _ _ F eq_refl D) ].

Section WithFP15.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP15.
Ltac stepi F D :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
        exact (step_addi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
        exact (step_andi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) =>
        exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) =>
        exact (step_xori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_SLT _ _ _, _) =>
        exact (step_slti _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) =>
        exact (step_sltiu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
        exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
        exact (step_sub _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_AND _ _ _, _) =>
        exact (step_and _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_OR _ _ _, _) =>
        exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_XOR _ _ _, _) =>
        exact (step_xor _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLL _ _ _, _) =>
        exact (step_sll _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SRL _ _ _, _) =>
        exact (step_srl _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SRA _ _ _, _) =>
        exact (step_sra _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLT _ _ _, _) =>
        exact (step_slt _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLTU _ _ _, _) =>
        exact (step_sltu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_ADD _ _ _, _) =>
        exact (step_addw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SUB _ _ _, _) =>
        exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SLL _ _ _, _) =>
        exact (step_sllw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SRL _ _ _, _) =>
        exact (step_srlw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SRA _ _ _, _) =>
        exact (step_sraw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm32 _ _ _, _) =>
        exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
        exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
        exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) =>
        exact (step_srai _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SLL _ _ _, _) =>
        exact (step_slliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SRL _ _ _, _) =>
        exact (step_srliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SRA _ _ _, _) =>
        exact (step_sraiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Auipc _ _, _) =>
        exact (step_auipc _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Lui _ _, _) =>
        exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MUL _ _ _, _) =>
        exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULH _ _ _, _) =>
        exact (step_mulh _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULHSU _ _ _, _) =>
        exact (step_mulhsu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULHU _ _ _, _) =>
        exact (step_mulhu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_DIV _ _ _, _) =>
        exact (step_div _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_REM _ _ _, _) =>
        exact (step_rem _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_DIVU _ _ _, _) =>
        eapply step_divu;
        [ exact F | reflexivity | exact D | try first [ assumption | lia ] ]
    | decode_any _ = Some (Mul M_REMU _ _ _, _) =>
        eapply step_remu;
        [ exact F | reflexivity | exact D | try first [ assumption | lia ] ]
    | decode_any _ = Some (Mul32 M_MUL _ _ _, _) =>
        exact (step_mulw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_DIV _ _ _, _) =>
        exact (step_divw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_DIVU _ _ _, _) =>
        exact (step_divuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_REM _ _ _, _) =>
        exact (step_remw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_REMU _ _ _, _) =>
        exact (step_remuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | _ => stepi_search F D
    end
  | step_simpl ].

Section WithFP16.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP16.
Ltac stepiv F D vv tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
        eapply step_addi_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
        eapply step_andi_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) =>
        eapply step_ori_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) =>
        eapply step_xori_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) =>
        eapply step_sltiu_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
        eapply step_slli_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
        eapply step_srli_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) =>
        eapply step_srai_at with (v := vv)
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
        eapply step_add_at with (v := vv)
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
        eapply step_sub_at with (v := vv)
    | decode_any _ = Some (OpImm32 _ _ _, _) =>
        eapply step_addiw_at with (v := vv)
    | decode_any _ = Some (Mul M_MUL _ _ _, _) =>
        eapply step_mul_at with (v := vv)
    | decode_any _ = Some (Lui _ _, _) =>
        eapply step_lui_at with (v := vv)
    | decode_any _ = Some (Auipc _ _, _) =>
        eapply step_auipc_at with (v := vv)
    | _ => eapply step_addi_at with (v := vv)
    end;
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP17.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP17.
Ltac stepiwv F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_addiw_at with (v := vv);
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP18.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP18.
Ltac stepj F D :=
  chain_step;
  [ reflexivity
  | first [ exact (step_jal_x0 _ _ _ _ _ _ _ F eq_refl D)
          | exact (step_jal_link _ _ _ _ _ _ _ _ F eq_refl D) ]
  | step_simpl ].

Section WithFP19.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP19.
Ltac stepjr F D tv tac :=
  chain_step;
  [ reflexivity
  | first [ eapply step_jalr_x0 with (tgt := tv);
            [ exact F | reflexivity | exact D | tac ]
          | eapply step_jalr_link with (tgt := tv);
            [ exact F | reflexivity | exact D | reflexivity | tac ] ]
  | step_simpl ].

Section WithFP20.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u_Z2bv : forall z, (0 <= z)%Z -> (z < 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. apply Z.mod_small. split; [exact Hlo|].
  exact Hhi.
Qed.

(* [comment removed for export] *)
Lemma v_addi_m1 : forall x, (1 <= bv_unsigned x)%Z ->
  v_addi x (-1) = Z_to_bv 64 (bv_unsigned x - 1).
Proof. intros x H1. apply (v_addi_m x 1); lia. Qed.

Lemma v_addi_m16 : forall x, (16 <= bv_unsigned x)%Z ->
  v_addi x (-16) = Z_to_bv 64 (bv_unsigned x - 16).
Proof. intros x H16. apply (v_addi_m x 16); lia. Qed.

Lemma v_addi_m32 : forall x, (32 <= bv_unsigned x)%Z ->
  v_addi x (-32) = Z_to_bv 64 (bv_unsigned x - 32).
Proof. intros x H32. apply (v_addi_m x 32); lia. Qed.

Lemma v_addi_m48 : forall x, (48 <= bv_unsigned x)%Z ->
  v_addi x (-48) = Z_to_bv 64 (bv_unsigned x - 48).
Proof. intros x H48. apply (v_addi_m x 48); lia. Qed.

Lemma v_addi_m64 : forall x, (64 <= bv_unsigned x)%Z ->
  v_addi x (-64) = Z_to_bv 64 (bv_unsigned x - 64).
Proof. intros x H64. apply (v_addi_m x 64); lia. Qed.

Lemma v_addi_m80 : forall x, (80 <= bv_unsigned x)%Z ->
  v_addi x (-80) = Z_to_bv 64 (bv_unsigned x - 80).
Proof. intros x H80. apply (v_addi_m x 80); lia. Qed.

(* [comment removed for export] *)
Lemma v_addi_nneg_t : forall x imm, (0 <= imm)%Z ->
  (bv_unsigned x + imm < 2^64)%Z ->
  v_addi x imm = Z_to_bv 64 (bv_unsigned x + imm).
Proof. intros x imm _ _. reflexivity. Qed.

(* [comment removed for export] *)
End WithFP20.
Ltac u_norm := repeat rewrite u_Z2bv by lia.

Section WithFP21.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP21.
Ltac imm_norm :=
  repeat match goal with
  | |- context [bv_signed ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_signed b) in
          change (bv_signed b) with v
      end
  | |- context [bv_unsigned ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_unsigned b) in
          change (bv_unsigned b) with v
      end
  end.

Section WithFP22.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP22.
Ltac sp_norm :=
  imm_norm;
  repeat (match goal with
  | |- context [v_addi ?x ?i] =>
      lazymatch x with
      | context [v_addi _ _] => fail
      | _ => first [ rewrite (v_addi_m80 x) by (u_norm; lia)
                   | rewrite (v_addi_m64 x) by (u_norm; lia)
                   | rewrite (v_addi_m48 x) by (u_norm; lia)
                   | rewrite (v_addi_m32 x) by (u_norm; lia)
                   | rewrite (v_addi_m16 x) by (u_norm; lia)
                   | rewrite (v_addi_m1 x) by (u_norm; lia)
                   | rewrite (v_addi_nneg_t x i) by (u_norm; lia) ]
      end
  end; u_norm; cbn [Z.to_N]).

Section WithFP23.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP23.
Ltac stepi_at F D val :=
  chain_step;
  [ reflexivity
  | eapply step_addi_at with (v := val);
    [ exact F | reflexivity | exact D
    | reflexivity
    | getr_resolve; regupd_resolve; reduce_bv_eqb_ifs; sp_norm;
      first [ reflexivity | lia | f_equal; lia
            | apply bv_eq;
              lazymatch goal with |- ?g => check_closed_term g end;
              vm_compute; reflexivity ] ]
  | step_simpl ].

Section WithFP24.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP24.
Ltac bveq :=
  apply bv_eq;
  lazymatch goal with
  | |- ?g =>
      tryif check_closed_term g then
        first
          [ (vm_compute; reflexivity)
          | fail 1 "bveq: vm_compute did not close this closed goal: "
                   "its two sides compute to different values." ]
      else tryif has_evar g then
        fail 1 "bveq: the goal contains an evar — vm_compute must not "
               "see it; instantiate the machine state (eexists / "
               "chain_step) before normalizing."
      else
        (* [comment removed for export] *)
        first
          [ reflexivity
          | fail 1 "bveq: the goal is OPEN (it mentions a context "
                   "variable) and kernel conversion did not close it — "
                   "resolve the register and memory projections first "
                   "(getr_resolve, regupd_resolve) and try again." ]
  end.

Section WithFP25.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Goal v_addi (Z_to_bv 64 5) 3 = Z_to_bv 64 8.
Proof. bveq. Abort.
Goal forall regs (v : word), getr (regupd regs 11 v) 11 = v.
Proof. intros. assert_fails bveq. getr_resolve. reflexivity. Abort.

(* [comment removed for export] *)
Goal forall v : word, exists w : word, w = v.
Proof.
  intros v. eexists.
  check_closed_term (v_addi (Z_to_bv 64 5) 3).
  assert_fails (check_closed_term (v_addi v 4)).
  lazymatch goal with |- ?g => assert_fails (check_closed_term g) end.
  set (k := Z_to_bv 64 7).
  check_closed_term (v_addi k 1).
  set (k2 := v_addi v 1).
  assert_fails (check_closed_term (v_addi k2 1)).
  let u := vm_eval (bv_unsigned (v_addi (Z_to_bv 64 5) 3)) in
  lazymatch u with 8%Z => idtac end.
  (* [comment removed for export] *)
  try (let u := vm_eval (bv_unsigned (v_addi v 4)) in
       fail 1 "vm_eval accepted an open term").
Abort.

(* [comment removed for export] *)
Goal forall v : word, v_addi v 4 = v_addi v 4.
Proof. intros v. wlit (v_addi v 4). wlits. reflexivity. Abort.
Goal forall v : word,
  (v_addi (Z_to_bv 64 5) 3, v_addi v 4) = (Z_to_bv 64 8, v_addi v 4).
Proof.
  intros v. wlits.
  lazymatch goal with |- (@BV _ _ _, _) = _ => idtac end.
  f_equal. bveq.
Abort.

(* [comment removed for export] *)
End WithFP25.
Ltac stepw_addr :=
  getr_resolve; regupd_resolve; sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].
Ltac stepw_val :=
  getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs;
  first [ reflexivity | sp_norm; first [ reflexivity | f_equal; lia ] | bveq ].

(* [comment removed for export] *)
Ltac stepw_addr_hyps :=
  getr_resolve; regupd_resolve;
  repeat match goal with
  | H : Sem.reg_get ?R ?r = _ |- context [Sem.reg_get ?R ?r] => rewrite H
  end;
  imm_norm; rewrite ?v_addi_0;
  sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].

Section WithFP27.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP27.
Ltac stepw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val
        | reflexivity | oktac ]
    end
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepsd F D aexp vexp vtac oktac :=
  step_intro;
  [ reflexivity
  | eapply step_sd_at with (a := aexp) (v := vexp);
    [ exact F | reflexivity | exact D | stepw_addr_hyps | vtac | oktac ]
  | step_simpl ].

Ltac stepld F D aexp vexp readtac :=
  step_intro;
  [ reflexivity
  | eapply step_ld with (bs := word_to_le_bytes 8 vexp) (v := vexp);
    [ exact F | reflexivity | exact D
    | match goal with |- rdn _ _ ?ad _ = _ =>
        replace ad with aexp by stepw_addr_hyps
      end; readtac
    | exact (bytes_le_to_Z_8 _) ]
  | step_simpl ].

Section WithFP28.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP28.
Ltac vm_refl_bv :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section WithFP29.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP29.
Ltac wlit_closed p :=
  check_closed_term p;
  let u := vm_eval (bv_unsigned p) in
  replace p with (Z_to_bv 64 u) by bveq.

Section WithFP30.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP30.
Ltac wlits_closed :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_closed (v_addi a b)
  | |- context [v_add ?a ?b] => wlit_closed (v_add a b)
  | |- context [v_sub ?a ?b] => wlit_closed (v_sub a b)
  end.

Section WithFP32.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP32.
Ltac rdn_ext_lit :=
  erewrite rdn_ext;
    [ (* [comment removed for export] *)
    | imm_norm; u_norm; lia
    | let x := fresh "x" in
      let Hx := fresh "Hx" in
      intros x Hx; revert Hx; imm_norm; u_norm; intros Hx ].

Section WithFP33.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma byte_nz_u : forall b : byte, b <> Z_to_bv 8 0 -> (bv_unsigned b <> 0)%Z.
Proof.
  intros b Hb Hc. apply Hb. apply bv_eq. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u_zext8 : forall b : byte,
  bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof.
  intro b. apply u_Z2bv; pose proof (u8_range b); lia.
Qed.

(* [comment removed for export] *)
Lemma zext8_byte : forall b : byte,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = b.
Proof.
  intro b. apply bv_eq.
  rewrite Z_to_bv_unsigned, u_zext8.
  apply bv_wrap_small. pose proof (u8_range b).
  change (bv_modulus 8) with 256%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma byte_neq_lit_u : forall (b : byte) (z : Z), (0 <= z < 256)%Z ->
  b <> Z_to_bv 8 z -> (bv_unsigned b <> z)%Z.
Proof.
  intros b z Hz Hb Hc. apply Hb. apply bv_eq.
  rewrite Hc, Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Z.mod_small; [reflexivity |].
  change (bv_modulus 8) with 256%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma c_eq_zext_lit_false : forall (b : byte) (z : Z), (0 <= z < 256)%Z ->
  b <> Z_to_bv 8 z ->
  c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 z) = false.
Proof.
  intros b z Hz Hb. unfold c_eq, bv_eqb. apply Z.eqb_neq.
  rewrite u_zext8, u_Z2bv by lia.
  exact (byte_neq_lit_u b z Hz Hb).
Qed.

(* [comment removed for export] *)
Lemma u_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  bv_unsigned (nat_to_word n) = Z.of_nat n.
Proof. intros n Hn. unfold nat_to_word. apply u_Z2bv; lia. Qed.

(* [comment removed for export] *)
Lemma word_add_nat : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp_r.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma word_add_nat_0 : forall x : word, x + nat_to_word 0 = x.
Proof.
  intro x. apply bv_eq. rewrite word_add_nat.
  rewrite u_Z2bv by (pose proof (u64_range x); lia). lia.
Qed.

(* [comment removed for export] *)
Lemma word_add_nat_1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word m) 1 = a + nat_to_word (S m).
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_add_nat_m1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word (S m)) (-1) = a + nat_to_word m.
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma v_add_comm : forall x y : word, v_add x y = y + x.
Proof.
  intros x y. apply bv_eq.
  change (v_add x y) with (x + y).
  rewrite !bv_add_unsigned. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma v_add_wrap : forall x y : word,
  (2^64 <= bv_unsigned x + bv_unsigned y)%Z ->
  v_add x y = Z_to_bv 64 (bv_unsigned x + bv_unsigned y - 2^64).
Proof.
  intros x y Hw. unfold v_add. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- (Z.mod_add (bv_unsigned x + bv_unsigned y - 2^64) 1 (2^64)) by lia.
  f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma v_sub_0_neg : forall y : word,
  v_sub (Z_to_bv 64 0) y = Z_to_bv 64 (- bv_unsigned y).
Proof.
  intro y. unfold v_sub.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  f_equal.
Qed.

(* [comment removed for export] *)
Lemma u_neg_small : forall z : Z, (0 < z)%Z -> (z <= 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 (- z)) = (2^64 - z)%Z.
Proof.
  intros z Hz0 Hz. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  replace (- z)%Z with ((2^64 - z) + (-1) * 2^64)%Z by lia.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma v_addi_neg_S : forall d : nat,
  v_addi (Z_to_bv 64 (- Z.of_nat (S d))) 1 = Z_to_bv 64 (- Z.of_nat d).
Proof.
  intro d. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma block_head_size_le : forall rseq argv envp,
  (Z.of_nat (block_head_size rseq argv envp)
   <= 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 512)%Z.
Proof.
  intros rseq argv envp.
  unfold block_head_size, block_items, auxv_size, auxv_count.
  pose proof (Nat.mod_upper_bound
                (length argv + length envp + 3) 2 ltac:(lia)).
  destruct rseq; lia.
Qed.

Lemma launch_sp_le_top : forall inp (top sp : word),
  valid_launch_sp top inp sp ->
  (bv_unsigned sp <= bv_unsigned top)%Z.
Proof.
  intros inp top sp [_ [_ Hhi]].
  unfold launch_sp_hi, align_down16 in Hhi.
  pose proof (Nat2Z.is_nonneg
    (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Z.mod_pos_bound
    (bv_unsigned top - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp))) 16 ltac:(lia)).
  lia.
Qed.

Lemma launch_top_minus_sp : forall inp (top sp : word),
  valid_launch inp ->
  valid_launch_sp top inp sp ->
  (bv_unsigned top - bv_unsigned sp <= 2101782)%Z.
Proof.
  intros inp top sp [_ Hb] [_ [Hlo _]].
  unfold launch_bytes, e2big_limit in Hb.
  unfold launch_sp_lo, align_down16 in Hlo.
  pose proof (block_head_size_le (kb_rseq (in_kernel inp))
                (in_argv inp) (in_envp inp)).
  pose proof (Z.mod_pos_bound
    (bv_unsigned top - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp))
     - 4095) 16 ltac:(lia)).
  lia.
Qed.

Lemma bsb_bound : forall v inp mbase ph entry (sp brk : word) draw,
  valid_launch inp ->
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
   <= 2101782)%Z.
Proof.
  intros v inp mbase ph entry sp brk draw Hvl Hlau.
  rewrite (length_entry_stack_image_launch v inp mbase ph entry sp brk draw
             Hlau).
  destruct Hlau as (_ & Hsp & _).
  exact (launch_top_minus_sp inp (ed_top draw) sp Hvl Hsp).
Qed.

(* [comment removed for export] *)
Lemma range_avoids_two : forall (s0 s1 : Segment) (a n : Z),
  Z.ltb a (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) = false ->
  Z.ltb a (Z.of_N (seg_base s1) + Z.of_N (seg_size s1)) = false ->
  range_avoids_ro_segs [s0; s1] a n = true.
Proof.
  intros s0 s1 a n H0 H1. unfold range_avoids_ro_segs. cbn [forallb].
  rewrite H0, H1. rewrite !andb_false_r. cbn [negb]. rewrite !orb_true_r.
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition ro_segs_below (segs : list Segment) (data_base : Z) : bool :=
  forallb (fun seg =>
             seg_writable seg
             || Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) data_base)
          segs.

Lemma range_avoids_ro_above : forall (segs : list Segment) (data_base addr n : Z),
  ro_segs_below segs data_base = true ->
  (data_base <= addr)%Z ->
  range_avoids_ro_segs segs addr n = true.
Proof.
  intros segs data_base addr n Hbelow Haddr.
  unfold ro_segs_below in Hbelow. unfold range_avoids_ro_segs.
  rewrite forallb_forall in *. intros seg Hin.
  specialize (Hbelow seg Hin).
  destruct (seg_writable seg) eqn:W; cbn [orb] in *; [reflexivity|].
  apply Z.leb_le in Hbelow.
  apply negb_true_iff. apply andb_false_iff. right.
  apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section DispatchSmoke.
  Variable segs : list Segment.
  Variable regs : bvmap 5 word.
  Variable mem rom : word -> option byte.

  (* [comment removed for export] *)
  Ltac smoke enc sh :=
    let F := fresh "F" in
    intro F;
    let D := fresh "D" in
    assert (D : decode_any enc = Some (sh, 4%Z)) by vm_refl_bv;
    eexists; stepi F D; apply mst_refl.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00152513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00152513 : bv 32) (OpImm ALU_SLT 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40155513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40155513 : bv 32) (ShiftImm ALU_SRA 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B57533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B57533 : bv 32) (Op ALU_AND 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B56533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B56533 : bv 32) (Op ALU_OR 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B54533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B54533 : bv 32) (Op ALU_XOR 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B51533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B51533 : bv 32) (Op ALU_SLL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B55533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B55533 : bv 32) (Op ALU_SRL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40B55533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40B55533 : bv 32) (Op ALU_SRA 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B52533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B52533 : bv 32) (Op ALU_SLT 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B53533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B53533 : bv 32) (Op ALU_SLTU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5053B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5053B : bv 32) (Op32 ALU_ADD 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5153B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5153B : bv 32) (Op32 ALU_SLL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5553B : bv 32) (Op32 ALU_SRL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40B5553B : bv 32) (Op32 ALU_SRA 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015051B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015051B : bv 32) (OpImm32 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015151B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015151B : bv 32) (ShiftImm32 ALU_SLL 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015551B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015551B : bv 32) (ShiftImm32 ALU_SRL 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x4015551B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x4015551B : bv 32) (ShiftImm32 ALU_SRA 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B51533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B51533 : bv 32) (Mul M_MULH 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B52533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B52533 : bv 32) (Mul M_MULHSU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B53533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B53533 : bv 32) (Mul M_MULHU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B54533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B54533 : bv 32) (Mul M_DIV 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B56533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B56533 : bv 32) (Mul M_REM 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5053B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5053B : bv 32) (Mul32 M_MUL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5453B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5453B : bv 32) (Mul32 M_DIV 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5553B : bv 32) (Mul32 M_DIVU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5653B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5653B : bv 32) (Mul32 M_REM 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5753B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5753B : bv 32) (Mul32 M_REMU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B55533 : bv 32) ->
    (bv_unsigned (getr regs 11) <> 0)%Z ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F NZ.
    assert (D : decode_any (0x02B55533 : bv 32)
                = Some (Mul M_DIVU 10 10 11, 4%Z)) by vm_refl_bv.
    eexists. stepi F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B57533 : bv 32) ->
    (bv_unsigned (getr regs 11) <> 0)%Z ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F NZ.
    assert (D : decode_any (0x02B57533 : bv 32)
                = Some (Mul M_REMU 10 10 11, 4%Z)) by vm_refl_bv.
    eexists. stepi F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00151513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x00151513 : bv 32)
                = Some (ShiftImm ALU_SLL 10 10 1, 4%Z)) by vm_refl_bv.
    eexists. stepiv F D (v_slli (getr regs 10) 1) ltac:(reflexivity).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00157513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x00157513 : bv 32)
                = Some (OpImm ALU_AND 10 10 1, 4%Z)) by vm_refl_bv.
    eexists. stepiv F D (v_andi (getr regs 10) 1) ltac:(reflexivity).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A13023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 8%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A13023 : bv 32)
                = Some (Store SZ8 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A12023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 4%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A12023 : bv 32)
                = Some (Store SZ4 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A11023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 2%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A11023 : bv 32)
                = Some (Store SZ2 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A10023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 1%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A10023 : bv 32)
                = Some (Store SZ1 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0080006F : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x0080006F : bv 32)
                = Some (Jal 0 8, 4%Z)) by vm_refl_bv.
    eexists. stepj F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x008000EF : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x008000EF : bv 32)
                = Some (Jal 1 8, 4%Z)) by vm_refl_bv.
    eexists. stepj F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00008067 : bv 32) ->
    getr regs 1 = (0x20000 : word) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F R.
    assert (D : decode_any (0x00008067 : bv 32)
                = Some (Jalr 0 1 0, 4%Z)) by vm_refl_bv.
    eexists. stepjr F D (0x20000 : word) ltac:(exact R).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x000500E7 : bv 32) ->
    getr regs 10 = (0x20000 : word) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F R.
    assert (D : decode_any (0x000500E7 : bv 32)
                = Some (Jalr 1 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepjr F D (0x20000 : word) ltac:(exact R).
    apply mst_refl.
  Abort.

End DispatchSmoke.
End WithFP33.

End StepTac.
From Stdlib Require ZArith List Lia. From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType RiscvSemantics StackLayout State Run. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.
Module StoreOk.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout State Run.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.Footprint.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition mem_grows (m m' : word -> option byte) : Prop :=
  forall x, m x <> None -> m' x <> None.

Lemma mem_grows_refl : forall m, mem_grows m m.
Proof. intros m x H. exact H. Qed.

Lemma mem_grows_trans : forall m1 m2 m3,
  mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H12 H23 x Hx. apply H23, H12, Hx. Qed.

(* [comment removed for export] *)
Lemma wview_grows : forall segs m m' x,
  mem_grows m m' ->
  wview segs m x <> None -> wview segs m' x <> None.
Proof.
  intros segs m m' x Hg Hx. unfold wview in *.
  destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
  destruct (m x) as [b|] eqn:Hm.
  - exfalso. apply (Hg x); [rewrite Hm; discriminate|exact Hm'].
  - exact Hx.
Qed.

Lemma store_ok_mono : forall segs n m m' a,
  mem_grows m m' ->
  store_ok segs m a n = true -> store_ok segs m' a n = true.
Proof.
  intros segs n; induction n as [|n IH]; intros m m' a Hg H; [reflexivity|].
  cbn [store_ok] in *.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  destruct (wview segs m' a) as [b'|] eqn:Hv'.
  - apply (IH m m'); assumption.
  - exfalso. apply (wview_grows segs m m' a Hg); [rewrite Hv; discriminate|exact Hv'].
Qed.

(* [comment removed for export] *)

Lemma wbytes_grows : forall bs m a, mem_grows m (wbytes m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [wbytes]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_zeros_grows : forall zs m, mem_grows m (apply_zeros m zs).
Proof.
  intros zs m x Hx. unfold apply_zeros.
  destruct zs as [|z zs']; [exact Hx|].
  destruct (zeros_cover (z :: zs') x); [discriminate|exact Hx].
Qed.

Lemma zmem_grows : forall m b l, mem_grows m (zmem m b l).
Proof.
  intros m b l x Hx. unfold zmem.
  destruct (Z.leb _ _ && Z.ltb _ _)%bool; [discriminate|exact Hx].
Qed.

Lemma write_to_mem_grows : forall bs m a, mem_grows m (write_to_mem m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [write_to_mem]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_writes_grows : forall ws m, mem_grows m (apply_writes m ws).
Proof.
  induction ws as [|w ws' IH]; intros m x Hx.
  - exact Hx.
  - destruct w as [a bs]. cbn [apply_writes].
    apply IH. apply write_to_mem_grows. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_all : forall segs n m a,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      wview segs m x <> None) ->
  store_ok segs m a n = true.
Proof.
  intros segs n; induction n as [|n IH]; intros m a Hnw Hall; [reflexivity|].
  cbn [store_ok].
  destruct (wview segs m a) as [b|] eqn:Hv.
  2: { exfalso. refine (Hall a _ Hv). rewrite Nat2Z.inj_succ. lia. }
  (* [comment removed for export] *)
  destruct n as [|n']; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hnw.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
    by (apply u_add1; rewrite Nat2Z.inj_succ in Hnw; lia).
  apply IH.
  - rewrite Hu1. lia.
  - intros x Hx. rewrite Hu1 in Hx. apply Hall.
    rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Lemma wrap_mem_window_defined :
  forall inp mbase ph entry sp (x : word) draw,
  stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned x ->
  bv_unsigned x < bv_unsigned sp ->
  wrap_mem inp mbase ph entry sp draw x <> None.
Proof.
  intros inp mbase ph entry sp x draw Hlo Hhi. unfold wrap_mem.
  destruct (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw) x)
    as [b|]; [discriminate|].
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  cbn. discriminate.
Qed.

Lemma store_ok_wrap_window :
  forall segs inp mbase ph entry sp a n draw,
  stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
  store_ok segs (wrap_mem inp mbase ph entry sp draw) a n = true.
Proof.
  intros segs inp mbase ph entry sp a n draw Hlo Hhi.
  assert (Hsp : bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
  apply store_ok_of_all; [lia|].
  intros x Hx. unfold wview.
  destruct (wrap_mem inp mbase ph entry sp draw x) as [b|] eqn:Hw;
    [discriminate|].
  exfalso. revert Hw. apply wrap_mem_window_defined; lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_zeros_hit : forall segs m zs a n,
  zs <> [] ->
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      zeros_cover zs x = true) ->
  store_ok segs (apply_zeros m zs) a n = true.
Proof.
  intros segs m zs a n Hne Hnw Hcov.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, apply_zeros.
  destruct zs as [|z zs']; [contradiction|].
  rewrite (Hcov x Hx). discriminate.
Qed.

(* [comment removed for export] *)
Lemma store_ok_zmem : forall segs m (b l a : word) (n : nat),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
  store_ok segs (zmem m b l) a n = true.
Proof.
  intros segs m b l a n Hnw Hlo Hhi.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  cbn. discriminate.
Qed.

(* [comment removed for export] *)
Definition store_grant_ok (segs : list Segment) (m : word -> option byte)
                    (b l : word) : Prop :=
  forall (a : word) (n : nat),
    bv_unsigned b <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
    store_ok segs m a n = true.

Lemma store_grant_zmem : forall segs m b l,
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  store_grant_ok segs (zmem m b l) b l.
Proof.
  intros segs m b l Hnw a n Hlo Hhi. apply store_ok_zmem; lia.
Qed.

(* [comment removed for export] *)
Lemma store_grant_zmem_prefix : forall segs m b logical physical,
  (bv_unsigned logical <= bv_unsigned physical)%Z ->
  (bv_unsigned b + bv_unsigned physical <= 2 ^ 64)%Z ->
  store_grant_ok segs (zmem m b physical) b logical.
Proof.
  intros segs m b logical physical Hle Hnw a n Hlo Hhi.
  apply store_ok_zmem; lia.
Qed.

Lemma store_grant_mono : forall segs m m' b l,
  mem_grows m m' -> store_grant_ok segs m b l -> store_grant_ok segs m' b l.
Proof.
  intros segs m m' b l Hg H a n Hlo Hhi.
  eapply store_ok_mono; [exact Hg|]. apply H; assumption.
Qed.

(* [comment removed for export] *)
Lemma store_ok_seg_writable : forall segs m a n,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      exists seg,
        find_segment segs (bv_unsigned x) 1 = Some seg /\
        seg_writable seg = true /\
        segment_byte_at (seg_bytes seg)
                    (Z.to_N (bv_unsigned x - Z.of_N (seg_base seg))) <> None) ->
  store_ok segs m a n = true.
Proof.
  intros segs m a n Hnw Hall.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview.
  destruct (m x) as [b|]; [discriminate|].
  destruct (Hall x Hx) as [seg [Hfind [Hw Hb]]].
  rewrite Hfind, Hw. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma store_ok_wseg : forall segs m a n,
  wseg_ok segs a n = true -> store_ok segs m a n = true.
Proof.
  intros segs m a n; revert a m; induction n as [|n IH]; intros a m H; [reflexivity|].
  cbn [wseg_ok] in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
  apply andb_true_iff in H as [H Hrec].
  apply andb_true_iff in H as [Hwr Hbyte].
  destruct (segment_byte_at (seg_bytes seg)
              (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
    [|discriminate].
  cbn [store_ok]. unfold wview at 1.
  destruct (m a) as [b0|]; [apply IH, Hrec|].
  rewrite Hseg, Hwr, Hb. apply IH, Hrec.
Qed.

(* [comment removed for export] *)
Lemma store_ok_all : forall segs m n a,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok segs m a n = true ->
  forall x : word,
    bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
    wview segs m x <> None.
Proof.
  intros segs m n; induction n as [|n IH]; intros a Hnw H x Hx;
    [cbn in Hx; lia|].
  cbn [store_ok] in H.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  rewrite Nat2Z.inj_succ in Hnw, Hx.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  { assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Hv. discriminate. }
  (* [comment removed for export] *)
  assert (Hn : (1 <= Z.of_nat n)%Z) by lia.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
  (* [comment removed for export] *)
  eapply IH; [ | exact H | ]; lia.
Qed.

Lemma store_ok_sub : forall segs m (lo a : word) (N n : nat),
  bv_unsigned lo + Z.of_nat N <= 2 ^ 64 ->
  store_ok segs m lo N = true ->
  bv_unsigned lo <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned lo + Z.of_nat N ->
  store_ok segs m a n = true.
Proof.
  intros segs m lo a N n Hnw Hok Hl Hh.
  apply store_ok_of_all; [lia|].
  intros x Hx. apply (store_ok_all segs m N lo Hnw Hok). lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_window : forall segs m (lo a : word) (N n : nat) (base hi : Z),
  bv_unsigned lo = base ->
  base + Z.of_nat N = hi ->
  hi <= 2 ^ 64 ->
  wseg_ok segs lo N = true ->
  base <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= hi ->
  store_ok segs m a n = true.
Proof.
  intros segs m lo a N n base hi Hbase Htop Hnw Hw Hl Hh.
  eapply store_ok_sub; [ | apply store_ok_wseg, Hw | | ]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_read_aux : forall segs m n (a : word),
  store_ok segs m a n = true ->
  exists w, read_bytes_aux (wview segs m) a n = Some w.
Proof.
  intros segs m n; induction n as [|n IH]; intros a H.
  - exists []. reflexivity.
  - cbn [store_ok] in H. cbn [read_bytes_aux].
    destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
    destruct (IH (a + 1)%bv H) as [w Hw]. rewrite Hw. exists (b :: w). reflexivity.
Qed.

Lemma store_ok_wbuf : forall segs ms (buf cnt : word),
  store_ok segs (ms_mem ms) buf (word_to_nat cnt) = true ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms buf cnt H.
  rewrite read_bytes_map_eq. unfold ms_writable_byte.
  apply store_ok_read_aux. exact H.
Qed.

(* [comment removed for export] *)
Lemma of_nat_word_to_nat : forall w : word,
  Z.of_nat (word_to_nat w) = bv_unsigned w.
Proof.
  intro w. unfold word_to_nat. pose proof (u64_range w). lia.
Qed.

(* [comment removed for export] *)
Lemma store_grant_wbuf : forall segs ms (b l buf cnt : word),
  store_grant_ok segs (ms_mem ms) b l ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms b l buf cnt Hg Hlo Hhi.
  apply store_ok_wbuf, Hg; rewrite ?of_nat_word_to_nat; lia.
Qed.

(* [comment removed for export] *)
Lemma heap_rg_wbuf : forall segs ms (b l buf cnt : word) (cur : Z),
  store_grant_ok segs (ms_mem ms) b l ->
  cur <= bv_unsigned b + bv_unsigned l - bv_unsigned b ->
  covers (heap_rg b cur) buf (word_to_nat cnt) ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms b l buf cnt cur Hg Hcur Hc.
  destruct Hc as [Hlo Hhi]. cbn [heap_rg rg_lo rg_hi] in Hlo, Hhi.
  rewrite of_nat_word_to_nat in Hhi.
  eapply store_grant_wbuf; [exact Hg | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma zmem_wbuf : forall segs ms m (b l buf cnt : word),
  mem_grows (zmem m b l) (ms_mem ms) ->
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms m b l buf cnt Hgr Hnw Hlo Hhi.
  eapply store_grant_wbuf; [ | exact Hlo | exact Hhi ].
  eapply store_grant_mono; [exact Hgr|]. apply store_grant_zmem. exact Hnw.
Qed.

(* [comment removed for export] *)
Example drain_buffer_in_grant : forall segs ms m (b l buf cnt : word) a bs,
  ms_mem ms = wbytes (zmem m b l) a bs ->
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms m b l buf cnt a bs Hm Hnw Hlo Hhi.
  eapply zmem_wbuf;
    [ rewrite Hm; apply wbytes_grows | exact Hnw | exact Hlo | exact Hhi ].
Qed.

(* [comment removed for export] *)
Ltac store_ok_peel :=
  repeat first
    [ eapply store_ok_mono; [apply wbytes_grows|]
    | eapply store_ok_mono; [apply write_to_mem_grows|]
    | eapply store_ok_mono; [apply apply_zeros_grows|]
    | eapply store_ok_mono; [apply apply_writes_grows|] ].

(* [comment removed for export] *)
Definition stack_window_reach : Z := 2244095.

Definition stack_window_depth : Z := stack_max_size - stack_window_reach.

Lemma stack_window_depth_val : stack_window_depth = 6144513.
Proof. vm_compute. reflexivity. Qed.

Lemma page_round_up_Z_aligned : forall n,
  (n mod page_size = 0)%Z -> page_round_up_Z n = n.
Proof.
  intros n Hn. unfold page_round_up_Z, page_size in *.
  apply Z.mod_divide in Hn; [|lia]. destruct Hn as [k Hk]. subst n.
  replace (k * 4096 + 4096 - 1)%Z with (k * 4096 + 4095)%Z by lia.
  rewrite Z.div_add_l by lia.
  replace (4095 / 4096)%Z with 0%Z by reflexivity. lia.
Qed.

Lemma mmap_gap_sv48 : forall kb,
  mmap_gap Sv48 kb
  = (let g := (stack_max_size + (stack_guard_gap_bytes kb
                 + if kb_aslr kb then stack_rnd_max else 0))%Z in
     if (g <? mmap_min_gap)%Z then mmap_min_gap else g).
Proof.
  intros kb. pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  unfold mmap_gap. cbv zeta.
  rewrite Z.mod_small
    by (unfold two_pow_64, stack_max_size, stack_rnd_max;
        destruct (kb_aslr kb); lia).
  assert (Hmax : mmap_max_gap Sv48 = 117281240296105%Z)
    by (vm_compute; reflexivity).
  rewrite !Hmax.
  unfold mmap_min_gap in *. rewrite !Z.gtb_ltb.
  (* the kernel's own overflow guard [gap + pad > gap] first: [pad] is
     never negative, so it decides the branch and the remaining tests
     are between a closed form and literals *)
  destruct (kb_aslr kb); cbv beta iota delta [andb];
  [ destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + stack_rnd_max))%Z
      eqn:Ein
  | destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + 0))%Z
      eqn:Ein ];
  try apply Z.ltb_lt in Ein; try apply Z.ltb_ge in Ein;
  cbv beta iota delta [andb];
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota delta [andb]);
  unfold stack_max_size, stack_rnd_max in *; lia.
Qed.

Lemma mmap_gap_sv48_mod : forall kb,
  (mmap_gap Sv48 kb mod page_size = 0)%Z.
Proof.
  intros kb.
  assert (H4096 : forall x : Z, ((4096 * x) mod 4096 = 0)%Z)
    by (intro x; rewrite Z.mul_comm; apply Z_mod_mult).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold stack_guard_gap_bytes, mmap_min_gap, stack_max_size,
    stack_rnd_max, page_size.
  destruct (_ <? _)%Z;
    [ replace (128 * 1024 * 1024)%Z with (4096 * 32768)%Z by reflexivity;
      apply H4096 |].
  destruct (kb_aslr kb);
    [ replace (8 * 1024 * 1024
               + (4096 * stack_guard_gap_pages kb + 1073737728))%Z
        with (4096 * (264191 + stack_guard_gap_pages kb))%Z by lia
    | replace (8 * 1024 * 1024 + (4096 * stack_guard_gap_pages kb + 0))%Z
        with (4096 * (2048 + stack_guard_gap_pages kb))%Z by lia ];
    apply H4096.
Qed.

Lemma stack_window_lo_ge_sp : forall inp (sp brk0 mbase : word) draw,
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  (bv_unsigned sp - stack_max_size
   <= stack_window_lo (in_kernel inp) mbase draw)%Z.
Proof.
  intros inp sp brk0 mbase draw (_ & Hsp & _).
  pose proof (launch_sp_le_top inp (ed_top draw) sp Hsp).
  unfold stack_window_lo.
  apply Z.le_trans with (bv_unsigned (ed_top draw) - stack_max_size)%Z;
    [lia | apply Z.le_max_l].
Qed.

Lemma launch_base_gap_le : forall kb mbase,
  valid_launch_base Sv48 kb mbase ->
  (bv_unsigned mbase + stack_guard_gap_bytes kb
   <= va_stack_top Sv48
      - (if kb_aslr kb then 0x407ff000 else 8 * 1024 * 1024))%Z.
Proof.
  intros kb mbase (r & Hr & _ & _ & Heq).
  pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  rewrite Heq. unfold mmap_base_of.
  assert (Hdiv : (page_size
                  | va_stack_top Sv48 - mmap_gap Sv48 kb - page_size * r)%Z).
  { apply Z.divide_sub_r; [apply Z.divide_sub_r|].
    - exists 34359738368%Z. vm_compute. reflexivity.
    - apply Z.mod_divide; [unfold page_size; lia|]. apply mmap_gap_sv48_mod.
    - exists r. unfold page_size. lia. }
  rewrite page_round_up_Z_aligned
    by (apply Z.mod_divide; [unfold page_size; lia | exact Hdiv]).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold mmap_min_gap, va_stack_top, sp_window_hi, stack_max_size,
    stack_rnd_max, page_size in *.
  destruct (kb_aslr kb); cbv beta iota;
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota);
  lia.
Qed.

Lemma stack_window_lo_valid : forall inp (sp brk0 mbase : word) draw,
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  stack_window_lo (in_kernel inp) mbase draw
  <= bv_unsigned sp + stack_window_reach - stack_max_size.
Proof.
  intros inp sp brk0 mbase draw Hlaunch (Htop & Hsp & Hbase).
  pose proof (launch_top_minus_sp inp (ed_top draw) sp Hlaunch Hsp) as Hd.
  pose proof (launch_base_gap_le (in_kernel inp) mbase Hbase) as Hg.
  destruct Htop as (_ & Hhi & Hlo).
  unfold stack_window_lo, stack_window_reach, stack_max_size,
    va_stack_top, sp_window_hi, stack_rnd_max, page_size in *.
  destruct (kb_aslr (in_kernel inp)); cbv beta iota in Hg, Hlo;
    apply Z.max_lub; lia.
Qed.

Lemma store_ok_wrap_window_valid :
  forall segs inp mbase ph entry (sp brk0 : word) a n draw,
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  bv_unsigned sp + stack_window_reach - stack_max_size <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
  store_ok segs (wrap_mem inp mbase ph entry sp draw) a n = true.
Proof.
  intros segs inp mbase ph entry sp brk0 a n draw Hvl Hlau Hlo Hhi.
  apply store_ok_wrap_window; [|exact Hhi].
  pose proof (stack_window_lo_valid inp sp brk0 mbase draw Hvl Hlau). lia.
Qed.

Ltac store_ok_base :=
  first
    [ eapply store_ok_wrap_window_valid;
      [ eassumption | eassumption
      | unfold stack_window_reach, stack_max_size; u_norm; lia
      | u_norm; lia ]
    | eapply store_ok_zeros_hit;
      [ discriminate | u_norm; lia | intros; u_norm; lia ]
    | apply store_ok_zmem; u_norm; lia ].

(* [comment removed for export] *)
Ltac solve_store_ok :=
  store_ok_peel;
  first [ store_ok_base
        | eapply store_ok_mono; [apply zmem_grows|];
          store_ok_peel; store_ok_base ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Create HintDb store_ok_db.

Ltac store_ok_grows := solve [ eauto with store_ok_db ].

Ltac solve_store_ok_inv :=
  first [ solve_store_ok
        | store_ok_peel;
          eapply store_ok_mono; [ store_ok_grows | ]; solve_store_ok ].

(* [comment removed for export] *)
Ltac solve_mem_grows :=
  repeat first
    [ solve [ eauto with store_ok_db ]
    | apply mem_grows_refl
    | eapply mem_grows_trans; [ | apply wbytes_grows ]
    | eapply mem_grows_trans; [ | apply zmem_grows ]
    | eapply mem_grows_trans; [ | apply write_to_mem_grows ]
    | eapply mem_grows_trans; [ | apply apply_zeros_grows ]
    | eapply mem_grows_trans; [ | apply apply_writes_grows ] ].

End StoreOk.
Module Hoare.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition at_ (base : word) (d : Z) : word := Z_to_bv 64 (bv_unsigned base + d).

Lemma at_0 : forall base, at_ base 0 = base.
Proof.
  intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma at_addi : forall base d e, v_addi (at_ base d) e = at_ base (d + e).
Proof.
  intros base d e. unfold at_, v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma at_btgt : forall base d e, btgt (at_ base d) e = at_ base (d + e).
Proof. intros. unfold btgt. apply at_addi. Qed.

(* [comment removed for export] *)
Lemma at_lit : forall (base : word) (d : Z) (a : word),
  Z_to_bv 64 (bv_unsigned base + d) = a -> at_ base d = a.
Proof. intros. assumption. Qed.

(* [comment removed for export] *)
Lemma at_at : forall base d e, at_ (at_ base d) e = at_ base (d + e).
Proof. exact at_addi. Qed.

(* [comment removed for export] *)
Lemma u_succ_shift : forall (a : word) (i : Z),
  Z_to_bv 64 (bv_unsigned (a + 1) + i) = Z_to_bv 64 (bv_unsigned a + (1 + i)).
Proof.
  intros a i. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma at_self : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. intros a. exact (at_0 a). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition assn := bvmap 5 word -> (word -> option byte) -> (word -> option byte) -> Prop.

(* [comment removed for export] *)
Definition regset := reg -> Prop.
Definition memset := word -> Prop.

Definition regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
  forall r, ~ C r -> getr regs' r = getr regs r.

Definition mem_agree (W : memset) (m m' : word -> option byte) : Prop :=
  forall x, ~ W x -> m' x = m x.

Lemma regs_agree_refl : forall C regs, regs_agree C regs regs.
Proof. intros C regs r _. reflexivity. Qed.

Lemma mem_agree_refl : forall W m, mem_agree W m m.
Proof. intros W m x _. reflexivity. Qed.

Lemma regs_agree_trans : forall C regs1 regs2 regs3,
  regs_agree C regs1 regs2 -> regs_agree C regs2 regs3 -> regs_agree C regs1 regs3.
Proof. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

Lemma mem_agree_trans : forall W m1 m2 m3,
  mem_agree W m1 m2 -> mem_agree W m2 m3 -> mem_agree W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

Lemma regs_agree_mono : forall (C C' : regset) regs regs',
  (forall r, C r -> C' r) -> regs_agree C regs regs' -> regs_agree C' regs regs'.
Proof. intros C C' regs regs' Hsub H r Hr. apply H. intro; apply Hr, Hsub; assumption. Qed.

Lemma mem_agree_mono : forall (W W' : memset) m m',
  (forall x, W x -> W' x) -> mem_agree W m m' -> mem_agree W' m m'.
Proof. intros W W' m m' Hsub H x Hx. apply H. intro; apply Hx, Hsub; assumption. Qed.

(* [comment removed for export] *)
Lemma regs_agree_upd : forall (C : regset) regs regs' r v,
  C r -> regs_agree C regs regs' -> regs_agree C regs (regupd regs' r v).
Proof.
  intros C regs regs' r v Hin H s Hs.
  rewrite getr_other by (intro Heq; subst; contradiction).
  apply H, Hs.
Qed.

Lemma mem_agree_wbytes : forall (W : memset) m m' a bs,
  (forall i, (0 <= i < Z.of_nat (length bs))%Z -> W (Z_to_bv 64 (bv_unsigned a + i))) ->
  mem_agree W m m' -> mem_agree W m (wbytes m' a bs).
Proof.
  intros W m m' a bs. revert m' a.
  induction bs as [|b bs IH]; intros m' a Hin H; cbn [wbytes] in *; [exact H|].
  assert (Ha : W a).
  { specialize (Hin 0%Z ltac:(cbn [length]; lia)). rewrite at_self in Hin. exact Hin. }
  apply IH.
  - intros i Hi. rewrite u_succ_shift. apply Hin. cbn [length] in *. lia.
  - intros x Hx. cbn beta. destruct (bv_eqb x a) eqn:Heq.
    + exfalso. apply Hx. unfold bv_eqb in Heq. apply Z.eqb_eq, bv_eq in Heq.
      subst x. exact Ha.
    + apply H, Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition triple (segs : list Segment)
                  (C : regset) (W : memset)
                  (P : assn) (a b : word) (Q : assn) : Prop :=
  forall regs mem rom, P regs mem rom ->
    exists regs' mem',
      msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
      /\ Q regs' mem' rom
      /\ regs_agree C regs regs'
      /\ mem_agree W mem mem'.

(* [comment removed for export] *)
Lemma triple_intro : forall segs C W P a b Q,
  (forall regs mem rom, P regs mem rom ->
     exists regs' mem',
       msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
       /\ Q regs' mem' rom
       /\ regs_agree C regs regs'
       /\ mem_agree W mem mem') ->
  triple segs C W P a b Q.
Proof. intros; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma triple_skip : forall segs C W P a, triple segs C W P a a P.
Proof.
  intros segs C W P a regs mem rom HP.
  exists regs, mem. split; [apply mst_refl|].
  split; [exact HP|]. split; [apply regs_agree_refl|apply mem_agree_refl].
Qed.

(* [comment removed for export] *)
Lemma triple_seq : forall segs C1 W1 C2 W2 P Q R a b c,
  triple segs C1 W1 P a b Q ->
  triple segs C2 W2 Q b c R ->
  triple segs (fun r => C1 r \/ C2 r) (fun x => W1 x \/ W2 x) P a c R.
Proof.
  intros segs C1 W1 C2 W2 P Q R a b c H1 H2 regs mem rom HP.
  destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
  destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
  exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
  split; [exact HR|]. split.
  - eapply regs_agree_trans;
      [ eapply regs_agree_mono; [|exact Hr1]
      | eapply regs_agree_mono; [|exact Hr2] ]; auto.
  - eapply mem_agree_trans;
      [ eapply mem_agree_mono; [|exact Hm1]
      | eapply mem_agree_mono; [|exact Hm2] ]; auto.
Qed.

(* [comment removed for export] *)
Lemma triple_conseq : forall segs C C' W W' P P' Q Q' a b,
  triple segs C W P a b Q ->
  (forall regs mem rom, P' regs mem rom -> P regs mem rom) ->
  (forall regs mem rom, Q regs mem rom -> Q' regs mem rom) ->
  (forall r, C r -> C' r) ->
  (forall x, W x -> W' x) ->
  triple segs C' W' P' a b Q'.
Proof.
  intros segs C C' W W' P P' Q Q' a b H HP HQ HC HW regs mem rom HP'.
  destruct (H _ _ _ (HP _ _ _ HP')) as (regs' & mem' & Hst & HQ0 & Hr & Hm).
  exists regs', mem'. split; [exact Hst|]. split; [apply HQ, HQ0|].
  split; [eapply regs_agree_mono; eauto | eapply mem_agree_mono; eauto].
Qed.

Lemma triple_seq_same : forall segs C W P Q R a b c,
  triple segs C W P a b Q ->
  triple segs C W Q b c R ->
  triple segs C W P a c R.
Proof.
  intros segs C W P Q R a b c H1 H2 regs mem rom HP.
  destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
  destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
  exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
  split; [exact HR|].
  split; [eapply regs_agree_trans; eassumption | eapply mem_agree_trans; eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition frameable (C : regset) (W : memset) (R : assn) : Prop :=
  forall regs mem rom regs' mem',
    regs_agree C regs regs' -> mem_agree W mem mem' ->
    R regs mem rom -> R regs' mem' rom.

(* [comment removed for export] *)
Lemma triple_frame : forall segs C W P Q R a b,
  triple segs C W P a b Q ->
  frameable C W R ->
  triple segs C W (fun regs mem rom => P regs mem rom /\ R regs mem rom) a b
                  (fun regs mem rom => Q regs mem rom /\ R regs mem rom).
Proof.
  intros segs C W P Q R a b H HR regs mem rom (HP & HRr).
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & Hr & Hm).
  exists regs', mem'. split; [exact Hst|].
  split; [split; [exact HQ | eapply HR; eassumption]|].
  split; assumption.
Qed.

(* [comment removed for export] *)
Lemma frameable_and : forall C W R1 R2,
  frameable C W R1 -> frameable C W R2 ->
  frameable C W (fun regs mem rom => R1 regs mem rom /\ R2 regs mem rom).
Proof. intros C W R1 R2 H1 H2 regs mem rom regs' mem' Hr Hm (A & B); split; eauto. Qed.

Lemma frameable_reg : forall (C : regset) W (r : reg) (v : word),
  ~ C r -> frameable C W (fun regs _ _ => getr regs r = v).
Proof.
  intros C W r v Hnc regs mem rom regs' mem' Hr _ Hv.
  rewrite (Hr r Hnc). exact Hv.
Qed.

(* [comment removed for export] *)
Lemma frameable_rdn : forall segs (C : regset) (W : memset) (a : word) (n : nat) bs,
  (forall i, (0 <= i < Z.of_nat n)%Z -> ~ W (Z_to_bv 64 (bv_unsigned a + i))) ->
  frameable C W (fun _ mem _ => rdn segs mem a n = Some bs).
Proof.
  intros segs C W a n bs Hdisj regs mem rom regs' mem' _ Hm Hrd.
  rewrite <- Hrd. clear Hrd bs. revert a Hdisj.
  induction n as [|n IH]; intros a Hdisj; [reflexivity|].
  assert (Ha : ~ W a).
  { specialize (Hdisj 0%Z ltac:(lia)). rewrite at_self in Hdisj. exact Hdisj. }
  cbn [rdn]. rewrite (Hm a Ha). rewrite IH; [reflexivity|].
  intros i Hi. rewrite u_succ_shift. apply Hdisj. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ret_ok (k : word) : Prop := v_jalr k 0 = k.

Lemma land_m2_even : forall z : Z, (z mod 2 = 0)%Z -> Z.land z (-2) = z.
Proof.
  intros z Hz.
  assert (Hl : Z.land z 1 = 0%Z).
  { replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
  replace (-2)%Z with (Z.lnot 1) by reflexivity.
  rewrite <- Z.ldiff_land.
  rewrite <- (Z.lor_ldiff_and z 1) at 2.
  rewrite Hl, Z.lor_0_r. reflexivity.
Qed.

Lemma ret_ok_even : forall k, (bv_unsigned k mod 2 = 0)%Z -> ret_ok k.
Proof.
  intros k Hk. unfold ret_ok, v_jalr, jalr_tgtZ.
  rewrite Z.add_0_r, land_m2_even by exact Hk.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Definition proc (segs : list Segment) (C : regset) (W : memset)
                (P : assn) (entry : word) (Q : assn) : Prop :=
  forall k : word, ret_ok k ->
    triple segs C W (fun regs mem rom => P regs mem rom /\ getr regs 1 = k) entry k Q.

(* [comment removed for export] *)
Definition ra_indep (P : assn) : Prop :=
  forall regs v mem rom, P regs mem rom -> P (regupd regs 1 v) mem rom.

(* [comment removed for export] *)
Lemma triple_call : forall segs C W P Q callsite entry ret,
  (forall regs mem rom,
     RiscvSemantics.step segs (mkst regs callsite mem rom)
       = MachineOk (mkst (regupd regs 1 ret) entry mem rom)) ->
  ret_ok ret ->
  ra_indep P ->
  proc segs C W P entry Q ->
  triple segs (fun r => C r \/ r = 1) W P callsite ret Q.
Proof.
  intros segs C W P Q callsite entry ret Hjal Hret HraP Hproc regs mem rom HP.
  assert (Hpre : P (regupd regs 1 ret) mem rom
                 /\ getr (regupd regs 1 ret) 1 = ret).
  { split; [apply HraP, HP|]. apply getr_same. reg_neq_tac. }
  destruct (Hproc ret Hret (regupd regs 1 ret) mem rom Hpre)
    as (regs' & mem' & Hst & HQ & Hr & Hm).
  exists regs', mem'. split.
  - eapply mst_step; [reflexivity | apply Hjal | exact Hst].
  - split; [exact HQ|]. split; [|exact Hm].
    intros r Hr0.
    assert (HnC : ~ C r) by tauto.
    assert (Hne : r <> 1) by tauto.
    rewrite (Hr r HnC), getr_other by exact Hne. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma triple_loop : forall segs C W (I : nat -> assn) (hd out : word) (Q : assn),
  (forall i, triple segs C W (I (S i)) hd hd (I i)) ->
  triple segs C W (I O) hd out Q ->
  forall n, triple segs C W (I n) hd out Q.
Proof.
  intros segs C W I hd out Q Hbody Hexit n.
  induction n as [|n IH]; [exact Hexit|].
  eapply triple_seq_same; [apply Hbody | exact IH].
Qed.

(* [comment removed for export] *)
Lemma triple_loop_measure :
  forall segs C W (I : nat -> assn) (hd out : word) (Q P : assn),
  (forall i, triple segs C W (I (S i)) hd hd (I i)) ->
  triple segs C W (I O) hd out Q ->
  (forall regs mem rom, P regs mem rom -> exists n, I n regs mem rom) ->
  triple segs C W P hd out Q.
Proof.
  intros segs C W I hd out Q P Hbody Hexit Hmeas regs mem rom HP.
  destruct (Hmeas _ _ _ HP) as (n & HI).
  exact (triple_loop segs C W I hd out Q Hbody Hexit n regs mem rom HI).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma triple_msteps : forall segs C W P a b Q regs mem rom,
  triple segs C W P a b Q -> P regs mem rom ->
  exists regs' mem',
    msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom) /\ Q regs' mem' rom.
Proof.
  intros segs C W P a b Q regs mem rom H HP.
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
  exists regs', mem'. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma triple_wexit : forall segs C W P a b Q bufs code regs mem rom,
  triple segs C W P a b Q ->
  P regs mem rom ->
  (forall regs' mem', Q regs' mem' rom ->
     to_wexit segs (mkst regs' b mem' rom) bufs code) ->
  to_wexit segs (mkst regs a mem rom) bufs code.
Proof.
  intros segs C W P a b Q bufs code regs mem rom H HP Hcont.
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
  eapply msteps_to_wexit; [exact Hst | apply Hcont, HQ].
Qed.
End WithFP1.


End Hoare.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
Module WalkTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint wf_chain (l : list (reg * word)) (R : bvmap 5 word) : bvmap 5 word :=
  match l with nil => R | cons (r, v) l' => regupd (wf_chain l' R) r v end.
Fixpoint wf_look (l : list (reg * word)) (r : reg) : option word :=
  match l with nil => None | cons (r', v) l' => if bv_eqb r r' then Some v else wf_look l' r end.
Lemma wf_getr_chain : forall l R r, bv_eqb r 0 = false ->
  getr (wf_chain l R) r = match wf_look l r with Some v => v | None => getr R r end.
Proof.
  induction l as [|[r' v] l IH]; intros R r Hr; cbn [wf_chain wf_look]; [reflexivity|].
  assert (Hr0 : r <> 0). { intros E. rewrite E in Hr. rewrite PropExec.bv_eqb_refl in Hr. discriminate Hr. }
  destruct (bv_eqb r r') eqn:E.
  - assert (r = r') as ->. { apply bv_eq. unfold bv_eqb in E. apply Z.eqb_eq in E. exact E. }
    apply PropExec.getr_same. exact Hr0.
  - rewrite PropExec.getr_other. { apply IH. exact Hr. }
    intros E2. rewrite E2 in E. rewrite PropExec.bv_eqb_refl in E. discriminate E.
Qed.
Ltac wf_chain_list RS := lazymatch RS with regupd ?R' ?r' ?v => let l := wf_chain_list R' in constr:(cons (r', v) l) | _ => constr:(@nil (reg * word)) end.
Ltac wf_chain_base RS := lazymatch RS with regupd ?R' _ _ => wf_chain_base R' | _ => RS end.
Ltac wf_find RS r := lazymatch RS with
  | regupd ?R' ?r' ?v => let b := eval vm_compute in (bv_eqb r r') in
      lazymatch b with true => v | false => wf_find R' r end
  | _ => constr:(getr RS r) end.
Ltac wf_gres_one :=
  match goal with
  | |- context [getr (regupd ?R0 ?r' ?v0) ?r] =>
      let RS := constr:(regupd R0 r' v0) in
      let z := eval vm_compute in (bv_eqb r 0) in
      lazymatch z with
      | true => change (getr RS r) with (Z_to_bv 64 0)
      | false =>
          let l := wf_chain_list RS in let B := wf_chain_base RS in
          let val := wf_find RS r in
          let H := fresh "gH" in
          pose proof (wf_getr_chain l B r (@eq_refl bool false) : getr RS r = val) as H;
          rewrite H; clear H
      end
  end.
Ltac gres_old :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ].
Ltac gres :=
  repeat wf_gres_one;
  lazymatch goal with |- context [getr (regupd _ _ _) _] => gres_old | _ => idtac end;
  lazymatch goal with |- context [getr _ 0%bv] => rewrite ?getr_zero | _ => idtac end.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Lemma v_add_0_r : forall x : word, v_add x (Z_to_bv 64 0) = x.
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Lemma v_add_0_l : forall x : word, v_add (Z_to_bv 64 0) x = x.
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_l. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac is_pos_lit p :=
  lazymatch p with
  | xH => idtac
  | xO ?q => is_pos_lit q
  | xI ?q => is_pos_lit q
  end.
Ltac is_Z_lit z :=
  lazymatch z with
  | Z0 => idtac
  | Zpos ?p => is_pos_lit p
  | Zneg ?p => is_pos_lit p
  end.

(* [comment removed for export] *)
Ltac val_lit v :=
  lazymatch v with
  | Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
  | @BV _ _ _ => fail
  | _ => wlit_closed v
  end.

(* [comment removed for export] *)
Ltac vals_lit :=
  repeat match goal with
         | |- context [regupd _ _ ?v] => val_lit v
         end.

(* [comment removed for export] *)
Ltac vnorm := gres; imm_norm;
  lazymatch goal with |- context [v_addi _ 0%Z] => rewrite ?v_addi_0 | _ => idtac end;
  lazymatch goal with |- context [v_add _ (Z_to_bv 64 0)] => rewrite ?v_add_0_r | _ => idtac end;
  lazymatch goal with |- context [v_add (Z_to_bv 64 0) _] => rewrite ?v_add_0_l | _ => idtac end;
  vals_lit.

(* [comment removed for export] *)
Ltac stepn F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
  | _ => stepi F D; vnorm
  end.

(* [comment removed for export] *)
Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv F D v := stepiv F D v vres.

(* [comment removed for export] *)
Ltac stepb_tk F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].

Ltac stepb_ft F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].

(* [comment removed for export] *)
Ltac cond_compute :=
  idtac;
  lazymatch goal with
  | |- ?g => check_closed_term g; vm_compute; reflexivity
  end.

(* [comment removed for export] *)
Ltac stepb F D :=
  first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].

(* [comment removed for export] *)
Ltac stepret F D k tac :=
  stepjr F D k ltac:(gres; tac);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      | Hk : v_jalr k 0 = k |- _ => rewrite Hk
      end;
  try (wlit (v_jalr k 0)).

(* [comment removed for export] *)
Ltac stepsd F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sd_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
    | gres; first [ reflexivity | assumption | symmetry; assumption ]
    | oktac ]
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepld F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
    | first [ apply bytes_le_to_Z_8 | reflexivity ] ]
  | step_simpl; vnorm ].

End WalkTac.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State.
Module Frame.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Frame () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsCeq_rewrite_relationI47Corelib5Lists7ListDef6Forall00I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib7Classes;EquivalenceEpointwise_equivalenceC59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:Proper_mapc59OSSVerify5KrLib7Mh_00387CatExec=flat_map_app'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00387CatExec9skipn_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_00387CatExec>flat_map_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_00387WallSim:u_len_wordC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordc59OSSVerify5KrLib7Mh_00388DrainSim5procsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim8out_tailC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSim7lh_nextC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSimGdrain_omni_strong_equivC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00388DrainSimBdrain_strong_equivC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indc59OSSVerify5KrLib7Mh_00385Frame7in_rngbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00385Frame6in_rngC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C47Corelib7Classes?RelationClasses=iff_ReflexiveC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib7Mh_00385Frame7outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01c59OSSVerify5KrLib7Mh_00387StoreOk>mem_grows_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00385Frame9frame_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00385Frame;outside_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387StoreOk?mem_grows_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00385Frame?frame_mod_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00385Frame@frame_mod_weakenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00c59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib7Mh_00387CatExec<wbytes_aboveC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib7Mh_00385Frame>wbytes_outsideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes3nat00C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedc59OSSVerify5KrLib7Mh_00385Frame>frame_mod_byteC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C49OSSVerify5KrLib8PropExec6u_add1C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Definition in_rng (a base : word) (len : Z) : Prop :=
  (bv_unsigned base <= bv_unsigned a < bv_unsigned base + len)%Z.

Definition in_rngb (a base : word) (len : Z) : bool :=
  (Z.leb (bv_unsigned base) (bv_unsigned a) && Z.ltb (bv_unsigned a) (bv_unsigned base + len))%bool.

Lemma in_rngb_spec : forall a base len, in_rngb a base len = true <-> in_rng a base len.
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["FPX_1"] "h05lemmah11Bh21Hh32H0h42H1h51ah64baseh73lenp;1p;2p;3p;4p;6p;;p;5p;9p-1R0g0000R1p4p710R2p9P0p1000\p4p710R3p9P0p1001HR4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p1001fR4p4p7210R5p9P0p1002Zp4p710p9P0p1003Ap4p710R6p9P0g003_R7p4p710R8p9P0p1004Yp4p710R9p8P0p10050p4p710R:p8P0p1005Pp4p710R0p8p1005mp4p70R;P9p8P;P2p8P;P3p8P;p1006]p4p710R9p8P;p10079p4p710R<p8P;p1007Wp4p7210R=p8P;P5p8P;P4p4p710R4p8P;p10084p4p710R>p8P;p1008dp4p710p8P;P6p8P;P8p8P;p1009Ep4p710p8p1009bp4p710R;P9p8P;P6p8p100:?p4p70R?P2p8P?P3p8P?p100:mp4p7210p8P?P9p8P?p100;Ip4p710p8P?p100<?p4p7210p8P?P;p8P?P<p8P?p100<np4p710p8P?P=p8P?p100=ip4p710p8P?p100>cp4p710p8P?P5p8P?P4p8P?p100?_p4p710p8P?P>p8P?P6p8P?p100@Yp4p7210p8P?P8p8P?P0p8P?p100AMp4p710p8P?p100BSp4p7210R@p8P?p100C0RAp4p7210RBp8P?p100CMp4p7210p8p100ClR?p6051001RCp100Dnp4p710RDp8PCP0p8PCPAp4p710RAp8P?p60521000R?P;p8P?P6p8P?P0p8P?PBp8p100EPp6051000R;p100FNp4p710REp8P;p100Fjp4p710RFp8P;PDp8P;P:p8p100GIRDp6051001RGP2p8PGP3p8PGPEp8PGPFp8PGP5p8PGP4p8PGP6p8PGP8p8PGPCp8PGP;p8PGP:p8PGP0p8PGPAp8PGp100HLp4p710RGp8PDp60521000RDP2p8PDP3p8PDP5p8PDP4p8PDP>p8PDP8p8PDP?p8PDP0p8PDPBp8p100Hkp4p7210RBP9p8PBP<p8PBP=p8PBP6p8PBp100IWp4p710p8PBp100J4p4p710p8PBp100K;p4p710p8p100LEp4p710P6p8p100L`p4p70RBP2p8PBP3p8PBP9p8PBP<p8PBP=p8PBP5p8PBP4p8PBP>p8PBP6p8PBP8p8P@P6p8p100MVp6051000R@p100NUp4p710p8P@P:p8PGP9p8PGP6p8p100OMp6051000RGP9p8PGP6p8p100PHp6051000R:P6p8P:PGp8p100QFp6051002R6P9p8P6P<p8P6P=p8P6PGp8P6P:p8p100RCp6051002RGP:p8PGP6p8p100SPp6051002RGP:p8PGP6p8g00TXj11Tg00U=j1LTg00U[j1ATg00V>j23Tg00Vhj2=Tg00WEj24Tg00Wbj2:Tg00X?j2<Tg00X]R6j22Tg00Y8RGj25Tg00YQj27Tg00Ymj26TP1j2KTg00ZIj2JTg00Zjj3ITg00[`j4;Tg00\SR1j6HTg00]Ej2DTg00]ej4CTg00^Ll;BTg00_Gj2@Tg00_gj49Tg00`Bj5ETg00`_j3?Tg00aYj3FTg00bRj3GTP7l9>Tg00blf0R7g00cL3Gp=0p-0R:PGg00clf5R=f4R<f3R9f2R@f1R8P7M9>p=8g00d]#1#1#1#1#1#1#LRB#AR>g00eB13B8R413B@R5'=R31447R2,:5RD'<#0%03R0%0DR?'2'513B9RA,=5R;1458RC,:ARF'<#0%0;R;%0FRF'2REP7175ARH16ACRC'2RIPI1K:IRJE8W01J3D1745RD,50PE12HFREP;PHP7PFPFP:PGg00e`9I:GR;PFC;EHPIPIPJE8W01D451652R4,5?PEPIP:P:^1:PGP:P:PGPGCCP6P1PHP:PGP;PHC;PFPCP7M;BPIPIPJE8W01@5212D4R4PI[RDPDPHPCPI13B<R<14A@'613B=RB,7<14<9,6BP8P7C9W4X3HP7DEX24R4P4C9O2O2O2A?@87#0AF@87'5eW7X6>W5o"). Qed.

Fixpoint outside (a : word) (rs : list (word * Z)) : Prop :=
  match rs with
  | [] => True
  | (b, n) :: rs' => ~ in_rng a b n /\ outside a rs'
  end.

Lemma outside_app : forall a rs1 rs2, outside a (rs1 ++ rs2) <-> outside a rs1 /\ outside a rs2.
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["FPX_1"] "p'0h02H0h12H2h21Hh32H1h43rs1h52H3h62H4h72H5h82H6h92IHh:1ah;2a0h<1bi001bh=1lh>1nh?3rs2i011pi021zp;1p;2p;4p;5p;3p-1R0p100fPp4p710R1p9P0p1000\p4p710R2p9P0p1001HR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001fR3p4p7210R4p9P0p1002Zp4p710p9P0p1003Ap4p710R5p9P0p100g3p4p710R6p9P0p1004Yp4p710R7p8P0p10050p4p710R8p8P0g005PR0p4p710R9p8p1005mp4p70R:P7p8P:P1p8P:P2p8P:p1006]p4p710R7p8P:p10079p4p710R;p8P:p1007Wp4p7210R<p8P:P4p8P:P3p4p710R3p8P:p10084p4p710R=p8P:p1008dp4p710p8P:P5p8P:P6p8P:p1009Ep4p710p8p1009bp4p710R:P7p8P:P5p8p100:?p4p70R>P1p8P>P2p8P>p100:mp4p7210p8P>P7p8P>p100;Ip4p710p8P>p100<?p4p7210p8P>P:p8P>P;p8P>p100<np4p710p8P>P<p8P>p100=ip4p710p8P>p100>cp4p710p8P>P4p8P>P3p8P>p100?_p4p710p8P>P=p8P>P5p8P>p100@Yp4p7210p8P>P6p8P>P9p8P>p100AMp4p710p8P>p100BSp4p7210R?p8P>p100C0R@p4p7210RAp8P>p100CMp4p7210p8p100ClR>p6051001RBg00DnRCp4p710RDp8PBP9p8PBP@p4p710R@p8P>p60521000R>P:p8P>P5p8P>P9p8P>PAp8p100EPp6051000R:p100FNp4p710REp8P:p100Fjp4p710RFp8P:PDp8P:P8p8p100GIRDp6051001RGP1p8PGP2p8PGPEp8PGPFp8PGP4p8PGP3p8PGP5p8PGP6p8PGPBp8PGP:p8PGP8p8PGP9p8PGP@p8PGp100HLp4p710RGp8PDp60521000RDP1p8PDP2p8PDP4p8PDP3p8PDP=p8PDP6p8PDP>p8PDP9p8PDPAp8p100Hkp4p7210RAP7p8PAP;p8PAP<p8PAP5p8PAp100IWp4p710p8PAp100J4p4p710p8PAp100K;p4p710p8p100LEp4p710P5p8p100L`p4p70RAP1p8PAP2p8PAP7p8PAP;p8PAP<p8PAP4p8PAP3p8PAP=p8PAP5p8PAP6p8P?P5p8p100MVp6051000R?p100NUp4p710p8P?P8p8PGP7p8PGP5p8p100OMp6051000RGP7p8PGP5p8p100PHp6051000R8P5p8P8PGp8p100QFp6051002R5P7p8P5P;p8P5P<p8P5PGp8P5P8p8p100RCp6051002RGP8p8PGP5p8p100SPp6051002RGP8p8PGP5p8g00TXj19Tg00U=j1DTg00U[j1?Tg00gkR5j2>Tg00hKj1CTg00hkj20Tg00Y8j25Tg00X]j21Tg00_gj44Tg00`Bj56Tg00iej1=Tg00jEj3<Tg00aYj37Tg00jej18TP0j3;Tg00k>j2BTg00k]j4@TPCj5ATf3RCf2R0f1RGf0R83;'0p=2100G/18p=310G8,10p=:g00d]#9#9#9#9#9#9#D#?R<g00eBR;,><R7#CR?P7PCP7P8PGC210CGR693C8'5X4?1008RAg00l=R=/16[11=AR3P6[P=P6g00lYP8C4X2AP=P6P6f4R6/00P8W3X0=P8D6X23C4P0P7%=7R3P8C2A303A'5eP5P<P;f5R5P7P8PCC2105C9358'5f6R3P7A<70GRAP6C21036933A'5[^=?P8f8RAP7P8P3C210A393A8'5f9R=P7PGf7R4C2R2f:R1101A730RD[R910=GR>10=4R@'1P1P7P0PAC2[A7=C0#8R:/1211:>/1@'5f;R:P7PCP=C2\D10:CRDf<R>/01R2P0f=RB/05RF10B:REPGP8C4O1W1W3PBP7P5P:C2RH\2\DA7>35#8RDA;7617:>RIA7B43#8RJ/1FRF/1ERK[A:D>6/12R211JHRD[PJPHPKf>RKP7P3P>C2P5P8O1R5f?RH/04R6?:HBf@RL/0ARM10LKRNA7L1=#8/1M/1NfARN/0HROP3PGO1fBR3/0LfCRPP7P:PNC2RQ[P8PGO1PQfDRQ?7KBRR#8RS10Q>RT'110Q3RUPSPTP4P8O1RVg00m5RW1BW8RXb7X0RPSePCC4P0C4b3b0W6X2MP8D6b0W5X1JP8D6X0IPFPEPD10K>A7H=A#8RAP6A;74B9:AHP5P3P7P1PLC2R1\OP8PCO1P1P=P8O110PN93P:PTPUA;7>39:SQfE/0PfFRP?7LHRL#8RHPPP7PKPQC2PVPWPXb8X1LPHePCC4W7X2TP8D6b1b3b1X6MX0APGD6W5X1FP8D6X02C4b3W0X29P8D6P=P7P<P;PCP0C@=<7GR0P4C2A3=0@'5eW9X4?X>;X<<PGP8O2n2001101000121100102X;7PGDAX??W4W:o"). Qed.

Definition frame_mod (mem mem' : word -> option byte) (rs : list (word * Z)) : Prop :=
  (forall a, outside a rs -> mem' a = mem a) /\ mem_grows mem mem'.

Lemma frame_mod_refl : forall mem rs, frame_mod mem mem rs.
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["FPX_1"] "h01ah13memh22rsp;1p;2p;3p;4p-1R0p100fPp4p710R1p9P0p1000\p4p710R2p9P0p1001HR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001fR3p4p7210R4p9P0p1002Zp4p710p9P0p1003Ap4p710R5p9P0p100g3p4p710R6p9P0p1004Yp4p710R7p8P0p10050p4p710R8p8P0p1005Pp4p710R0p8p1005mp4p70R9P7p8P9P1p8P9P2p8P9p1006]p4p710R7p8P9p10079p4p710R:p8P9p1007Wp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p10084p4p710R<p8P9p1008dp4p710p8P9P5p8P9P6p8P9p1009Ep4p710p8p1009bp4p710R9P7p8P9P5p8p100:?p4p70R=P1p8P=P2p8P=p100:mp4p7210p8P=P7p8P=p100;Ip4p710p8P=p100<?p4p7210p8P=P9p8P=P:p8P=p100<np4p710p8P=P;p8P=p100=ip4p710p8P=p100>cp4p710p8P=P4p8P=P3p8P=p100?_p4p710p8P=P<p8P=P5p8P=p100@Yp4p7210p8P=P6p8P=P0p8P=p100AMp4p710p8P=p100BSp4p7210R>p8P=p100C0R?p4p7210R@p8P=p100CMp4p7210p8p100ClR=p6051001RAp100Dnp4p710RBp8PAP0p8PAP?p4p710R?p8P=p60521000R=P9p8P=P5p8P=P0p8P=P@p8p100EPp6051000R9p100FNp4p710RCp8P9p100Fjp4p710RDp8P9PBp8P9P8p8p100GIRBp6051001REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HLp4p710REp8PBp60521000RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8p100Hkp4p7210R@P7p8P@P:p8P@P;p8P@P5p8P@p100IWp4p710p8P@p100J4p4p710p8P@p100K;p4p710p8p100LEp4p710P5p8p100L`p4p70R@P1p8P@P2p8P@P7p8P@P:p8P@P;p8P@P4p8P@P3p8P@P<p8P@P5p8P@P6p8P>P5p8p100MVp6051000R>p100NUp4p710p8P>P8p8PEP7p8PEP5p8p100OMp6051000REP7p8PEP5p8p100PHp6051000R8P5p8P8PEp8p100QFp6051002R5P7p8P5P:p8P5P;p8P5PEp8P5P8p8p100RCp6051002REP8p8PEP5p8p100SPp6051002REP8p8PEP5p8g00TXj10Tg00U=j12Tg00U[j11Tg00mRj13Tg00gkj2;Tg00hKj1:Tg00hkj29Tg00bRj34Tg00n4j25Tg00o2j26Tg00oLj17Tg00_gj48Tg00d]#0#0#0R5#0#0#0#2#1RE%25#1#3R5[g00eB,;E#:f0f1R8'9R;f3P8O1R:=45:[^0E1588165:V;X0E%78C8W2W1o"). Qed.

Lemma frame_mod_weaken : forall mem mem' rs rs',
  (forall a, outside a rs' -> outside a rs) -> frame_mod mem mem' rs -> frame_mod mem mem' rs'.
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["FPX_1"] "h01ah11Hh22Hah32Heh42Hgh52Hwh63memh74mem'h82rsh93rs'p;1p;2p;3p;4p-1R0p100fPp4p710R1p9P0p1000\p4p710R2p9P0p1001HR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001fR3p4p7210R4p9P0p1002Zp4p710p9P0p1003Ap4p710R5p9P0p100g3p4p710R6p9P0p1004Yp4p710R7p8P0p10050p4p710R8p8P0p1005Pp4p710R0p8p1005mp4p70R9P7p8P9P1p8P9P2p8P9p1006]p4p710R7p8P9p10079p4p710R:p8P9p1007Wp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p10084p4p710R<p8P9p1008dp4p710p8P9P5p8P9P6p8P9p1009Ep4p710p8p1009bp4p710R9P7p8P9P5p8p100:?p4p70R=P1p8P=P2p8P=p100:mp4p7210p8P=P7p8P=p100;Ip4p710p8P=p100<?p4p7210p8P=P9p8P=P:p8P=p100<np4p710p8P=P;p8P=p100=ip4p710p8P=p100>cp4p710p8P=P4p8P=P3p8P=p100?_p4p710p8P=P<p8P=P5p8P=p100@Yp4p7210p8P=P6p8P=P0p8P=p100AMp4p710p8P=p100BSp4p7210R>p8P=p100C0R?p4p7210R@p8P=p100CMp4p7210p8p100ClR=p6051001RAp100Dnp4p710RBp8PAP0p8PAP?p4p710R?p8P=p60521000R=P9p8P=P5p8P=P0p8P=P@p8p100EPp6051000R9p100FNp4p710RCp8P9p100Fjp4p710RDp8P9PBp8P9P8p8p100GIRBp6051001REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HLp4p710REp8PBp60521000RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8p100Hkp4p7210R@P7p8P@P:p8P@P;p8P@P5p8P@p100IWp4p710p8P@p100J4p4p710p8P@p100K;p4p710p8p100LEp4p710P5p8p100L`p4p70R@P1p8P@P2p8P@P7p8P@P:p8P@P;p8P@P4p8P@P3p8P@P<p8P@P5p8P@P6p8P>P5p8p100MVp6051000R>p100NUp4p710p8P>P8p8PEP7p8PEP5p8p100OMp6051000REP7p8PEP5p8p100PHp6051000R8P5p8P8PEp8p100QFp6051002R5P7p8P5P:p8P5P;p8P5PEp8P5P8p8p100RCp6051002REP8p8PEP5p8p100SPp6051002REP8p8PEP5p8g00TXj10Tg00U=j16Tg00U[j14Tg00mRj17Tg00gkj2:Tg00hKj19Tg00hkj21Tg010Oj35Tg00bRj32Tg00n4j23Tg00_gj48Tg00d]#0#0#0R5#0#0#0#6#4RE%65#4#7R5[R8g00eB,:E#9R;f0R:f1R7'1f3R>,17[^0Ef4R6f275>g00X]11:6f6R@P7O1f7R<P7O1525[^0Ef5R3/36A5@3>P:11:@f8R@P7O1f9R3P7O1525[^0E13@<11:<R6f:P7O1f;P7O1525[^0E133@P>P7P<P7P:O2O2X26X0EP:C8W4W3P7P:O2n2001000000120000000W1W5X9;W8X78W6o"). Qed.

Lemma frame_mod_trans : forall m1 m2 m3 rs1 rs2,
  frame_mod m1 m2 rs1 -> frame_mod m2 m3 rs2 -> frame_mod m1 m3 (rs1 ++ rs2).
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["FPX_1"] "h01ah11Hh23rs1h33rs2h42Hah52E1h62E2h72G1h82G2h92H1h:2H2h;2m1h<2m2h=2m3h>1op;1p;2p;3p;6p;5p;4p-1R0p100fPp4p710R1p9P0p1000\p4p710R2p9P0p1001HR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001fR3p4p7210R4p9P0p1002Zp4p710p9P0g003AR5p4p710R6p9P0p100g3p4p710R7p9P0p1004Yp4p710R8p8P0p10050p4p710R9p8P0g005PR0p4p710R:p8p1005mp4p70R;P8p8P;P1p8P;P2p8P;p1006]p4p710R8p8P;p10079p4p710R<p8P;p1007Wp4p7210R=p8P;P4p8P;P3p4p710R3p8P;p10084p4p710R>p8P;p1008dp4p710p8P;P6p8P;P7p8P;p1009Ep4p710p8p1009bp4p710R;P8p8P;P6p8p100:?p4p70R?P1p8P?P2p8P?p100:mp4p7210p8P?P8p8P?p100;Ip4p710p8P?p100<?p4p7210p8P?P;p8P?P<p8P?p100<np4p710p8P?P=p8P?p100=ip4p710p8P?p100>cp4p710p8P?P4p8P?P3p8P?p100?_p4p710p8P?P>p8P?P6p8P?p100@Yp4p7210p8P?P7p8P?P:p8P?p100AMp4p710p8P?p100BSp4p7210R@p8P?p100C0RAp4p7210RBp8P?p100CMp4p7210p8p100ClR?p6051001RCp100Dnp4p710RDp8PCP:p8PCPAp4p710RAp8P?p60521000R?P;p8P?P6p8P?P:p8P?PBp8p100EPp6051000R;p100FNp4p710REp8P;p100Fjp4p710RFp8P;PDp8P;P9p8p100GIRDp6051001RGP1p8PGP2p8PGPEp8PGPFp8PGP4p8PGP3p8PGP6p8PGP7p8PGPCp8PGP;p8PGP9p8PGP:p8PGPAp8PGp100HLp4p710RGp8PDp60521000RDP1p8PDP2p8PDP4p8PDP3p8PDP>p8PDP7p8PDP?p8PDP:p8PDPBp8p100Hkp4p7210RBP8p8PBP<p8PBP=p8PBP6p8PBp100IWp4p710p8PBp100J4p4p710p8PBp100K;p4p710p8p100LEp4p710P6p8p100L`p4p70RBP1p8PBP2p8PBP8p8PBP<p8PBP=p8PBP4p8PBP3p8PBP>p8PBP6p8PBP7p8P@P6p8p100MVp6051000R@p100NUp4p710p8P@P9p8PGP8p8PGP6p8p100OMp6051000RGP8p8PGP6p8p100PHp6051000R9P6p8P9PGp8p100QFp6051002R6P8p8P6P<p8P6P=p8P6PGp8P6P9p8p100RCp6051002RGP9p8PGP6p8p100SPp6051002RGP9p8PGP6p8g00TXj12Tg00U=j18Tg00U[j17Tg00mRj19Tg00gkj2?Tg00hKj1;Tg010Oj34Tg00hkj20Tg00bRj31Tg00n4j25TP0j33Tg00X]R0j26Tg011Kj3:TP5j6>Tg012Ij5=Tg00_gj4<Tg00d]#2#2#2R5#2#2#2#8#7R6%85#7#9R5[RGg00eB,?6R9#;R=f4R<f3R8f1R@34P0f0R7/08f6RBP@O1f7R>P@O1515[^06f5R3/5<f2R4943<A39<894>3[P71073f8R2P@O1f9R1P@O1515[^06152>A42>3P0107>f:P@O1f;RDP@O1515[^061512A392>94D1P71071f<R:P@O1f=R?P@O1515[^0615:DA39:D,07RDf>RAP@O1f@P@O1515[^0615A:P0A39@7,041084108@'6[R;104@1047'6A394@,08R9[10<810<4'6\9A:4@7P@n2001000000120000000X3=X2=X06P;^3=^2=^06P7P4PAP?P@O4104A104?'6P0f?,08108AfAR8P<O1fCP<O1515P7103810B8P5fEP>O1fGP2O19157X>5PAP>P@O2fDP>O1P1P>P7O2E>W:W9P@P7O2n2001000000120000000b4b1X4DX06PAP?P:P3P7D=C<W8W6P@P7O2n2001000000121000000W1W7W5P@P7O2n2001000000121000000W1X3=W2X=GX<GW;o"). Qed.

(* [comment removed for export] *)
Lemma frame_mod_trans_same : forall m1 m2 m3 rs,
  frame_mod m1 m2 rs -> frame_mod m2 m3 rs -> frame_mod m1 m3 rs.
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["FPX_1"] "h01ah13rs1h23rs2h31Hh42H1h52H2h62Hah72m1h82m2h92m3h:2rsp;1p;2p;3p;4p;7p;6p-1R0p100fPp4p710R1p9P0p1000\p4p710R2p9P0p1001HR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001fR3p4p7210R4p9P0p1002Zp4p710p9P0p1003Ap4p710R5p9P0p100g3p4p710R6p9P0p1004Yp4p710R7p8P0p10050p4p710R8p8P0g005PR0p4p710R9p8p1005mp4p70R:P7p8P:P1p8P:P2p8P:p1006]p4p710R7p8P:p10079p4p710R;p8P:p1007Wp4p7210R<p8P:P4p8P:P3p4p710R3p8P:p10084p4p710R=p8P:p1008dp4p710p8P:P5p8P:P6p8P:p1009Ep4p710p8p1009bp4p710R:P7p8P:P5p8p100:?p4p70R>P1p8P>P2p8P>p100:mp4p7210p8P>P7p8P>p100;Ip4p710p8P>p100<?p4p7210p8P>P:p8P>P;p8P>p100<np4p710p8P>P<p8P>p100=ip4p710p8P>p100>cp4p710p8P>P4p8P>P3p8P>p100?_p4p710p8P>P=p8P>P5p8P>p100@Yp4p7210p8P>P6p8P>P9p8P>p100AMp4p710p8P>p100BSp4p7210R?p8P>p100C0R@p4p7210RAp8P>p100CMp4p7210p8p100ClR>p6051001RBp100Dnp4p710RCp8PBP9p8PBP@p4p710R@p8P>p60521000R>P:p8P>P5p8P>P9p8P>PAp8p100EPp6051000R:p100FNp4p710RDp8P:p100Fjp4p710REp8P:PCp8P:P8p8p100GIRCp6051001RFP1p8PFP2p8PFPDp8PFPEp8PFP4p8PFP3p8PFP5p8PFP6p8PFPBp8PFP:p8PFP8p8PFP9p8PFP@p8PFp100HLp4p710RFp8PCp60521000RCP1p8PCP2p8PCP4p8PCP3p8PCP=p8PCP6p8PCP>p8PCP9p8PCPAp8p100Hkp4p7210RAP7p8PAP;p8PAP<p8PAP5p8PAp100IWp4p710p8PAp100J4p4p710p8PAp100K;p4p710p8p100LEp4p710P5p8p100L`p4p70RAP1p8PAP2p8PAP7p8PAP;p8PAP<p8PAP4p8PAP3p8PAP=p8PAP5p8PAP6p8P?P5p8p100MVp6051000R?p100NUp4p710p8P?P8p8PFP7p8PFP5p8p100OMp6051000RFP7p8PFP5p8p100PHp6051000R8P5p8P8PFp8p100QFp6051002R5P7p8P5P;p8P5P<p8P5PFp8P5P8p8p100RCp6051002RFP8p8PFP5p8p100SPp6051002RFP8p8PFP5p8g00TXj11Tg00U=j16Tg00U[j13Tg00mRj17Tg00gkj2=Tg00hKj1;Tg010Oj34TP0j32Tg00hkj20Tg00X]R0j25Tg011Kj38Tg00_gj49Tg013Mj7:Tg014Oj6<Tg00d]#1#1#1R5#1#1#1#6#3RF%65#3#7[R5g00eB,=FR8#;R<f3R;f2R7f0R?34f1R694;7f5RAP;A2877P710?;P0A286?,0710;710;6'5R0[1076107?'5A2876,0;[R=f4R3A28;7'0\0A876?P?n2001000000120000000X2<X1<X0FP=^2<^1<^0FP?P7PAPA107AR<P<P6P6C9O4b3W6X0FPAP3P;P7P7P6P?F:E<W5W4W:X95X85W7o"). Qed.

(* [comment removed for export] *)
Lemma wbytes_outside : forall bs m (base a : word),
  ~ in_rng a base (Z.of_nat (length bs)) ->
  (bv_unsigned base + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  wbytes m base bs a = m a.
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["FPX_1"] "h02Hah14__x1h24__x2h34__x3h41mh52Hbh63Hgeh73Hlth82Hnh97__arithh:4__ffh;6__sat0h<6__sat1h=8__varmaph>5__with?1ah@4basehA2bshB4cstrhC1op;1p;2p;3p;4p;6p;7p;5p;8p-1R0p100fPp4p710R1p9P0p1000\p4p710R2p9P0p1001HR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001fR3p4p7210R4p9P0p1002Zp4p710p9P0p1003Ap4p710R5p9P0p100g3p4p710R6p9P0p1004Yp4p710R7p8P0g0050R8p4p710R9p8P0p1005Pp4p710R0p8p1005mp4p70R:P7p8P:P1p8P:P2p8P:p1006]p4p710R7p8P:p10079p4p710R;p8P:p1007Wp4p7210R<p8P:P4p8P:P3p4p710R3p8P:p10084p4p710R=p8P:p1008dp4p710p8P:P5p8P:P6p8P:p1009Ep4p710p8p1009bp4p710R:P7p8P:P5p8p100:?p4p70R>P1p8P>P2p8P>p100:mp4p7210p8P>P7p8P>p100;Ip4p710p8P>p100<?p4p7210p8P>P:p8P>P;p8P>p100<np4p710p8P>P<p8P>p100=ip4p710p8P>p100>cp4p710p8P>P4p8P>P3p8P>p100?_p4p710p8P>P=p8P>P5p8P>p100@Yp4p7210p8P>P6p8P>P0p8P>p100AMp4p710p8P>p100BSp4p7210R?p8P>p100C0R@p4p7210RAp8P>p100CMp4p7210p8p100ClR>p6051001RBp100Dnp4p710RCp8PBP0p8PBP@p4p710R@p8P>p60521000R>P:p8P>P5p8P>P0p8P>PAp8p100EPp6051000R:p100FNp4p710RDp8P:p100Fjp4p710REp8P:PCp8P:P9p8p100GIRCp6051001RFP1p8PFP2p8PFPDp8PFPEp8PFP4p8PFP3p8PFP5p8PFP6p8PFPBp8PFP:p8PFP9p8PFP0p8PFP@p8PFp100HLp4p710RFp8PCp60521000RCP1p8PCP2p8PCP4p8PCP3p8PCP=p8PCP6p8PCP>p8PCP0p8PCPAp8p100Hkp4p7210RAP7p8PAP;p8PAP<p8PAP5p8PAp100IWp4p710p8PAp100J4p4p710p8PAp100K;p4p710p8p100LEp4p710P5p8p100L`p4p70RAP1p8PAP2p8PAP7p8PAP;p8PAP<p8PAP4p8PAP3p8PAP=p8PAP5p8PAP6p8P?P5p8p100MVp6051000R?p100NUp4p710p8P?P9p8PFP7p8PFP5p8p100OMp6051000RFP7p8PFP5p8p100PHp6051000R9P5p8P9PFp8p100QFp6051002R5P7p8P5P;p8P5P<p8P5PFp8P5P9p8p100RCp6051002RFP9p8PFP5p8p100SPp6051002RFP9p8PFP5p8g00TXj13Tg00U=j1@Tg00U[j1<Tg00hKj1=Tg00mRj1]TP8j25Tg015Rj14Tg00aYj3LTg00jej1ITg00V>j21Tg00WEj26Tg0162j1>Tg016Pj2ATg00YQj20Tg016mj2VTg00Ymj22Tg017RR8j2UTg017lj4TTg00bRj3:Tg018gj6OTg019hj1NTg01:Mj2MTg01;5j3KTg00iej1JTg01;Yj2;Tg01<7j4HTg01<Uj1FTg01=3j1GTg01=^j27Tg01>Aj1ETg01>fj49Tg01?Qj1DTg01@3j3CTg01@Vj7BTg01A:j6PTg01A^j2QTg00o2j2RTg01B@j2STg01Blj3\Tg01CKj4[Tg00X]j2ZTg01D=j5WTg01E>j7XTg01Ebj8YTf1R5g01FFRFg01FeR9P9g01GER<f0R;g01GeFXp=8f3R7PFP9P9P<f2R?P5P;GYp=?g00d]R6#3RA#3#3R=#@#<R3#=%3=#3#3R=#@R4#<R2%]3R1[1537#49L;5#I114?RCf4R0,53#4'6%>AR>%>=R='AR@'01147R:,VC12C:10:C'UP81140R8,2:108:f6R:f5RCf7RBP0CTP:P0O15:1P;114CRE,28f8RDPBP:PCP7P;EOW7P;O110E8PDPBP:PC153DR:#Ng01HERB%4:'01M>=12B>10B=12B@[[10B>R:g00l=REAK>=5UW010B@\E^0:f:R:PDO1P1g00eBR1g01HcRD#J%=DP11;1?P51;17CH%F1%G1RDP11716REg01IOR@%E6,71R6C9,8DR=%D9R>PDPDPFP9P9P<PDPFP9P9P<P=P1P6g01J6171A9C1EREC9,8DFBEPP>P1PEP@P6C9,8DC?C?1QD<P;P?g00blRDg00cLR<'R1S;?=:D<dA\1B5C[b:b=b>X11X21W310;?1057165?,27'Zg00m5[16?7/00[[^11^21^31P;114:f=,53#4f;,14PCf9O5b9b4b;b<bBDWW6P;O1n200100000021000011000bCW5W8X?2X@2W4WAo"). Qed.

Lemma frame_mod_wbytes : forall m base bs,
  (bv_unsigned base + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  frame_mod m (wbytes m base bs) [(base, Z.of_nat (length bs))].
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["FPX_1"] "h01ah11Hh22Hah32Hbh42_Hh54baseh62bsh71mp;1p;2p;4p;3p;6p-1R0p100fPp4p710R1p9P0p1000\p4p710R2p9P0p1001HR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001fR3p4p7210R4p9P0p1002Zp4p710p9P0p1003Ap4p710R5p9P0p100g3p4p710R6p9P0p1004Yp4p710R7p8P0g0050R8p4p710R9p8P0p1005Pp4p710R0p8p1005mp4p70R:P7p8P:P1p8P:P2p8P:p1006]p4p710R7p8P:p10079p4p710R;p8P:p1007Wp4p7210R<p8P:P4p8P:P3p4p710R3p8P:p10084p4p710R=p8P:p1008dp4p710p8P:P5p8P:P6p8P:p1009Ep4p710p8p1009bp4p710R:P7p8P:P5p8p100:?p4p70R>P1p8P>P2p8P>p100:mp4p7210p8P>P7p8P>p100;Ip4p710p8P>p100<?p4p7210p8P>P:p8P>P;p8P>p100<np4p710p8P>P<p8P>p100=ip4p710p8P>p100>cp4p710p8P>P4p8P>P3p8P>p100?_p4p710p8P>P=p8P>P5p8P>p100@Yp4p7210p8P>P6p8P>P0p8P>p100AMp4p710p8P>p100BSp4p7210R?p8P>p100C0R@p4p7210RAp8P>p100CMp4p7210p8p100ClR>p6051001RBp100Dnp4p710RCp8PBP0p8PBP@p4p710R@p8P>p60521000R>P:p8P>P5p8P>P0p8P>PAp8p100EPp6051000R:p100FNp4p710RDp8P:p100Fjp4p710REp8P:PCp8P:P9p8p100GIRCp6051001RFP1p8PFP2p8PFPDp8PFPEp8PFP4p8PFP3p8PFP5p8PFP6p8PFPBp8PFP:p8PFP9p8PFP0p8PFP@p8PFp100HLp4p710RFp8PCp60521000RCP1p8PCP2p8PCP4p8PCP3p8PCP=p8PCP6p8PCP>p8PCP0p8PCPAp8p100Hkp4p7210RAP7p8PAP;p8PAP<p8PAP5p8PAp100IWp4p710p8PAp100J4p4p710p8PAp100K;p4p710p8p100LEp4p710P5p8p100L`p4p70RAP1p8PAP2p8PAP7p8PAP;p8PAP<p8PAP4p8PAP3p8PAP=p8PAP5p8PAP6p8P?P5p8p100MVp6051000R?p100NUp4p710p8P?P9p8PFP7p8PFP5p8p100OMp6051000RFP7p8PFP5p8p100PHp6051000R9P5p8P9PFp8p100QFp6051002R5P7p8P5P;p8P5P<p8P5PFp8P5P9p8p100RCp6051002RFP9p8PFP5p8p100SPp6051002RFP9p8PFP5p8g00TXj10Tg00U=j1:Tg00U[j19Tg00mRj1>Tg00hKj1ITg00V>j2DTP8j21Tg015Rj12Tg00WEj2?Tg0162j16Tg016Pj2=Tg00YQj2<Tg00gkj2;Tg00k]j4HTg00iej1GTg00jEj3FTg00hkj23Tg017lj48j3CTg00bRj34Tg00n4j2BTg00aYj37Tg00jej15Tg01J]j6ATg01K^j3@Tg00_gj4ETg00d]#0R8#0#0R5#0#0#0RF#:R9#9R<%:5#9R5#>R;[%I5f1R7,D9f0R9,15#2'?%68%6F'='<g00eBRF,;<R8P<PFf3RFf2R?,15#2CH%G8R83F,39R6f5RAf4R=PFP7C8PAP7O154;[^0<ACF?7,BFg00X]115F#2977=#51378f6R3PAP=P?C8P3P?O154;P9115A#297F3#513=8f7f9f8PAP7P3EAW4W2P7P9O2n2001000000120000000X16X0<A@7F?CEW3W6X5<W7o"). Qed.

(* [comment removed for export] *)
Lemma frame_mod_store_ok : forall segs mem mem' rs a n,
  frame_mod mem mem' rs -> store_ok segs mem a n = true -> store_ok segs mem' a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["FPX_1"] "h01ah11Hh22H0h32Hgh42_Hh53memh64mem'h71nh82rsh94segsp;1p;2p;3p;4p;7p-1R0p100fPp4p710R1p9P0p1000\p4p710R2p9P0p1001HR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001fR3p4p7210R4p9P0p1002Zp4p710p9P0p1003Ap4p710R5p9P0p100g3p4p710R6p9P0p1004Yp4p710R7p8P0p10050p4p710R8p8P0p1005Pp4p710R0p8p1005mp4p70R9P7p8P9P1p8P9P2p8P9p1006]p4p710R7p8P9p10079p4p710R:p8P9p1007Wp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p10084p4p710R<p8P9p1008dp4p710p8P9P5p8P9P6p8P9p1009Ep4p710p8p1009bp4p710R9P7p8P9P5p8p100:?p4p70R=P1p8P=P2p8P=p100:mp4p7210p8P=P7p8P=p100;Ip4p710p8P=p100<?p4p7210p8P=P9p8P=P:p8P=p100<np4p710p8P=P;p8P=p100=ip4p710p8P=p100>cp4p710p8P=P4p8P=P3p8P=p100?_p4p710p8P=P<p8P=P5p8P=p100@Yp4p7210p8P=P6p8P=P0p8P=p100AMp4p710p8P=p100BSp4p7210R>p8P=p100C0R?p4p7210R@p8P=p100CMp4p7210p8p100ClR=p6051001RAp100Dnp4p710RBp8PAP0p8PAP?p4p710R?p8P=p60521000R=P9p8P=P5p8P=P0p8P=P@p8p100EPp6051000R9p100FNp4p710RCp8P9p100Fjp4p710RDp8P9PBp8P9P8p8p100GIRBp6051001REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HLp4p710REp8PBp60521000RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8p100Hkp4p7210R@P7p8P@P:p8P@P;p8P@P5p8P@p100IWp4p710p8P@p100J4p4p710p8P@p100K;p4p710p8p100LEp4p710P5p8p100L`p4p70R@P1p8P@P2p8P@P7p8P@P:p8P@P;p8P@P4p8P@P3p8P@P<p8P@P5p8P@P6p8P>P5p8p100MVp6051000R>p100NUp4p710p8P>P8p8PEP7p8PEP5p8p100OMp6051000REP7p8PEP5p8p100PHp6051000R8P5p8P8PEp8p100QFp6051002R5P7p8P5P:p8P5P;p8P5PEp8P5P8p8p100RCp6051002REP8p8PEP5p8p100SPp6051002REP8p8PEP5p8g00hKj18Tg00TXj10Tg00U=j14Tg00U[j17Tg00mRj1<Tg00gkj2;Tg010Oj3:Tg00hkj25Tg00bRj32Tg00n4j26Tg01L_j41Tg01M_j79Tg00blf0R5g00cL32p=3g01Na#8g00d]#0#0#0RE#0#0#0#4#7R8%4E#7#<RE[R;g00eB,;8#8g01O`f4R:f3R7f2R>3:g00X]155:f6R6f1R@O1f7R<P@O152E[^08f5R3/6:P<P6P7P>C1#3f8R>P6P:P7C1#3[P51556P>P@O1f9R7P@O152E[^0816><f:R>P7P6P3C1#3f;P6P>P7P<P@P5F9W1W3W4P@P5O2n2001000000120000000W2W7X08W8X6;W5W9o"). Qed.

Lemma frame_mod_byte : forall mem mem' rs a,
  frame_mod mem mem' rs -> outside a rs -> mem' a = mem a.
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["FPX_1"] "h01ah11Hh22Hah32Heh42_Hh53memh64mem'h72rsp;1p;2p;3p-1R0p100fPp4p710R1p9P0p1000\p4p710R2p9P0p1001HR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001fR3p4p7210R4p9P0p1002Zp4p710p9P0p1003Ap4p710R5p9P0p100g3p4p710R6p9P0p1004Yp4p710R7p8P0p10050p4p710R8p8P0p1005Pp4p710R0p8p1005mp4p70R9P7p8P9P1p8P9P2p8P9p1006]p4p710R7p8P9p10079p4p710R:p8P9p1007Wp4p7210R;p8P9P4p8P9P3p4p710R3p8P9p10084p4p710R<p8P9p1008dp4p710p8P9P5p8P9P6p8P9p1009Ep4p710p8p1009bp4p710R9P7p8P9P5p8p100:?p4p70R=P1p8P=P2p8P=p100:mp4p7210p8P=P7p8P=p100;Ip4p710p8P=p100<?p4p7210p8P=P9p8P=P:p8P=p100<np4p710p8P=P;p8P=p100=ip4p710p8P=p100>cp4p710p8P=P4p8P=P3p8P=p100?_p4p710p8P=P<p8P=P5p8P=p100@Yp4p7210p8P=P6p8P=P0p8P=p100AMp4p710p8P=p100BSp4p7210R>p8P=p100C0R?p4p7210R@p8P=p100CMp4p7210p8p100ClR=p6051001RAp100Dnp4p710RBp8PAP0p8PAP?p4p710R?p8P=p60521000R=P9p8P=P5p8P=P0p8P=P@p8p100EPp6051000R9p100FNp4p710RCp8P9p100Fjp4p710RDp8P9PBp8P9P8p8p100GIRBp6051001REP1p8PEP2p8PEPCp8PEPDp8PEP4p8PEP3p8PEP5p8PEP6p8PEPAp8PEP9p8PEP8p8PEP0p8PEP?p8PEp100HLp4p710REp8PBp60521000RBP1p8PBP2p8PBP4p8PBP3p8PBP<p8PBP6p8PBP=p8PBP0p8PBP@p8p100Hkp4p7210R@P7p8P@P:p8P@P;p8P@P5p8P@p100IWp4p710p8P@p100J4p4p710p8P@p100K;p4p710p8p100LEp4p710P5p8p100L`p4p70R@P1p8P@P2p8P@P7p8P@P:p8P@P;p8P@P4p8P@P3p8P@P<p8P@P5p8P@P6p8P>P5p8p100MVp6051000R>p100NUp4p710p8P>P8p8PEP7p8PEP5p8p100OMp6051000REP7p8PEP5p8p100PHp6051000R8P5p8P8PEp8p100QFp6051002R5P7p8P5P:p8P5P;p8P5PEp8P5P8p8p100RCp6051002REP8p8PEP5p8p100SPp6051002REP8p8PEP5p8g00TXj10Tg00U=j15Tg00U[j13Tg00mRj16Tg00gkj29Tg00hKj18Tg010Oj37Tg00hkj21Tg00bRj32Tg00n4j24Tg00d]#0#0#0R5#0#0#0#5#3RE%55#3#6R5[R8g00eB,9E#8f3R;f2R:f1R737g00X]f0R>/1;f5R6P7O1f6R@P7O1525[^0Ef4/4;11:;P6P;O1P@P;O1525[P>11>6f7R;P7O1f8P7O1525[^0E14;@116@P:P@P>O2W2W4W3P7P>O2n2001000000120000000W1X0EW7X68W5o"). Qed.

(* [comment removed for export] *)
Lemma frame_mod_rdn : forall segs mem mem' rs n (a : word),
  frame_mod mem mem' rs ->
  (forall i, (0 <= i < Z.of_nat n)%Z -> outside (Z_to_bv 64 (bv_unsigned a + i)) rs) ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn segs mem' a n = rdn segs mem a n.
Proof.
ltac2:(KReplay.run1 (kr_t_Frame ()) ["FPX_1"] "p'0h04__x1h11ih22H0h34__x2h41Hh51ah62Hbh73Hb0h82Hoh97__arithh:4__ffh;8__varmaph<5__with=4cstrh>1xi001xh?2IHh@1ni011nhA1zhB2HahC6__sat2hD6__sat3hE2H1hF2H2hG2HfhH3Hi0hI6__sat0hJ6__sat1hK1ohL1yhM3Ha1hN2HihO1bi021bhP1mhQ3memhR4mem'hS2n'hT2rshU4segsi034restp%0p&0p;1p;2p;3p;4p;6p;<p;Bp;7p;8p-1R0p100fPp4p710R1p9P0p1000\p4p710R2p9P0p1001HR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001fR3p4p7210R4p9P0p1002Zp4p710p9P0g003AR5p4p710R6p9P0p100g3p4p710R7p9P0p1004Yp4p710R8p8P0p10050p4p710R9p8P0p1005Pp4p710R0p8p1005mp4p70R:P8p8P:P1p8P:P2p8P:g006]R8p4p710R;p8P:p10079p4p710R<p8P:p1007Wp4p7210R=p8P:P4p8P:P3p4p710R3p8P:p10084p4p710R>p8P:p1008dp4p710p8P:P6p8P:P7p8P:p1009Ep4p710p8p1009bp4p710R:P;p8P:P6p8p100:?p4p70R?P1p8P?P2p8P?p100:mp4p7210p8P?P;p8P?p100;Ip4p710p8P?p100<?p4p7210p8P?P:p8P?P<p8P?p100<np4p710p8P?P=p8P?p100=ip4p710p8P?p100>cp4p710p8P?P4p8P?P3p8P?p100?_p4p710p8P?P>p8P?P6p8P?p100@Yp4p7210p8P?P7p8P?P0p8P?p100AMp4p710p8P?p100BSp4p7210R@p8P?p100C0RAp4p7210RBp8P?p100CMp4p7210p8p100ClR?p6051001RCp100Dnp4p710RDp8PCP0p8PCPAp4p710RAp8P?p60521000R?P:p8P?P6p8P?P0p8P?PBp8p100EPp6051000R:p100FNp4p710REp8P:p100Fjp4p710RFp8P:PDp8P:P9p8p100GIRDp6051001RGP1p8PGP2p8PGPEp8PGPFp8PGP4p8PGP3p8PGP6p8PGP7p8PGPCp8PGP:p8PGP9p8PGP0p8PGPAp8PGp100HLp4p710RGp8PDp60521000RDP1p8PDP2p8PDP4p8PDP3p8PDP>p8PDP7p8PDP?p8PDP0p8PDPBp8p100Hkp4p7210RBP;p8PBP<p8PBP=p8PBP6p8PBp100IWp4p710p8PBp100J4p4p710p8PBp100K;p4p710p8p100LEp4p710P6p8p100L`p4p70RBP1p8PBP2p8PBP;p8PBP<p8PBP=p8PBP4p8PBP3p8PBP>p8PBP6p8PBP7p8P@P6p8p100MVp6051000R@p100NUp4p710p8P@P9p8PGP;p8PGP6p8p100OMp6051000RGP;p8PGP6p8p100PHp6051000R9P6p8P9PGp8p100QFp6051002R6P;p8P6P<p8P6P=p8P6PGp8P6P9p8p100RCp6051002RGP9p8PGP6p8p100SPp6051002RGP9p8PGP6p8g00hKj1UTg00TXj1NTg00U=j1aTg00U[j1^Tg00mRR6j1jTg00gkk201Tg010Oj3MTg015RRGj12Tg00V>j23Tg00WER9j20Tg01P?j2CTg00hkj28Tg0162j1]Tg016Pk203Tg01Pej45Tg00bRj3;Tg00o2j2>Tg01QVR=j19Tg01R5j1xTg00YQR<j2=Tg00X]R;j2@Tg01Rlj3QTg00YmR@j24Tg01SRj1hTg01T0j6RTg01TYj4lTg01U<j4ETg019hj1OTg01:Mj2kTg01;5k308Tg00iek107Tg01;Yj2iTg01<Uk106Tg01=3k105Tg01Ucj2\Tg01=^j2fTg01?Qj1eTg01A^k200Tg01B@j2~Tg01Blj3}Tg01CKj4|Tg01VFj4YTg01W1j1{TP8j6VTg01WRj2zTg01XDj6yTg01YEj2cTg01Ygj2PTg01Z\j3wTg01[?j3HTg00jEj3bTg01[dj2WTg01\Mj3gTg01]6j2tTg01]bj1sTg01<7j4rTg01^@j3uTg01^cj2vTg01>fj4[TP5j6STg01_Wj4qTg01`8l<_Tg01`]l<ZTg01aBlBpTg01E>k702Tg01@3j3oTg01@Vj7nTg01Ebk804Tg01HER5f0R8'=p=1f2R7f1RB/48'@p=:107B/=8p=61458p=Ig00eBR>/>8p=7g01O`R3P3P>P>P=PGPGf3R=g01ahP7PBP8M<_p=?P3P>P>P>PGPGf5RGf4R4P=P7PBP8M<_p=BP>P>P@PGP@P4P5P5P=P7PBP8M<Zp=mP>P>P>P>P>P>P9P8PBP7P9P=P4PGf6R9f7R2f8R1f9RDMBpp=FA;>B8p=GP>P>P<P2P<P9PGP4P=P7PBP8M<Zp=JP>PBg01IOP8C[p=LPBg01FFR<g01FeR0P0g01GER?P8g01GeK02p=<Ao>B8p=AP>PBg01J6P8C[p=TP7P<P0P0P?PBP8Fnp=dP=P<P0P0P?P7PBP8L04p=K107B/08p=DP>P>P@P2P@P9PGP4P=P7PBP8M<Zp=X10B8,07p=`g01Na#Ug00d]R@#NR<#N#NRA#N#N#NR:#aRC#^RF%aA#^RA#jRE[S00Q00201F>#UAMG4=%18RH%2=RI7:8RJ13C=RK/0B,CCRL/89[^1>13C7RM%]<RN%]:R:+03RO76IRP%UARQ#jRRPDP2P=P4C5PDP1P=P4C53;[[[^5FS01X@3AM4=7g01bLRS#2RT9:H8RU18LG[^1>A6MTORTP1P2P=PSC5,>RW6W8WGX5FQ01AM9G4%94RV#2RW9:H818L2[^1>A6MWO%x=%1K?:KOP7P51=55RK%99S02#2RX#IRY'@%29RZ%]@R['0R\#IR],@KPKPYPKP]p-0R]/>K9QKKP8X>>RY14B8#hXL>X>>S031>>5PXP\PYPY%28#7X>3R^Q02P\108[S04X>>R_P9PZ%7ZC?R`EBEmER13C4Ra/0XRb/=OA6a\ORcPY1=B8#hXL>X>>RdPbPYP_PZO1RZO1Rb,0aPYPYPYP>P>g01bk10B8Cl#7XP>X@>RePaPa%7aPXPbPYPYP^Q02PZP`EBS05M:FPOPO%7OS061GOOeR`GJPBCEPc%O2%22Rc#11kN:RZ%IN%1:%IO[[Rf%1NRgg00l=RhB08N:BUWBR:%1O\h^BgRgP;13C1Rh#114hOf;Ri#2/0[S07#I,@KP4f:Rj,3CRk#113CiRl/4Og01HcRm$07Rn%UmRo1i>B&06>Rp&05>Rq1\>5Rr1f>@R@'L,<qS08%e0R01Lrr,<q1\>[Rs,A@Rt,Tr,<q5dqCK200q?R?P8P7g00blRug00cLRv'>1~87=;uvdA}>5BC|Rvb:b;b<X0>10B[Ru#I,@K\H^0>P8f?RK#2S09P2O2b9W2W4PBP8O2n2001000000120000000bIbJb=b7CYO210a5,CC/81P>13CGRa/051CC8S0:/8jXA>P8Pa%{aEV1CCa/8DPF13C9,CC188iXOFP8P91zC9EV189jf=Raf<R5PiP2P9P8Eyb2b2b2PDP4O1PjP4O15;EPEPiPGO1P6PAPRP6PAPEP81cA8Rw1Pa9Rxn10110000021010200P6PQPRf>RyP5g00lY9wC[Rz9HC2R{PDC5AbAB8,cQR|%eQR}n10110000021010300P}n10110000021010200P6PAPRP6PAPEP5P9O1PwPxn10110000021010200P6PQPRPyPaP{PDC5P|P}n10110000021010300P}n101100000210102005;RXKEP3AMa5i18Ly\J^1>fARJPKP=P4C5PJf@R{P=P4C55;R\P[[^5F%97RP#2Rx9:H813CDR~/0B,CC/8a[^1>A6hxOP6PAPRP6PAPEPKPDO1Pw1P{Dn10110000021010200S0;P6PQPRPJPKAHCjzRxP4C5P|P}n10110000021010300P}n10110000021010200P6PAPRQ0;P6PQPRPJP{PxP4C5P|P}n10110000021010300P}n101100000210102005;R]6]8]?P2AM5ij18La\U^1>P{PyP=PSC5P{PKP=PSC55;R\T[[^5F%9SRT#2RU9:H810hB,CC/85[^1>13C2?6UOP6PAPRP6PAPEPyP1O1Pw1PK1n10110000021010200P6PQPRP{PKAHCDzPSC5P|P}n10110000021010300P}n10110000021010200,>RW6W8W?AMya5%9=RU#2Rh9:H818LK[^1>A6MhOfBRhP{P=PVC5PhPJP=PVC55;R[[[^5F%9P#2RP9:H810kB,CC/8y[^1>A6~PO%9US0;#2RP,0kR~/=OADI[[=6kOS0<PYPdP~PYP_P_PIO1R~O1RMO1RL,0kPYPYPYPePkPk%7kPPPLPYPYP^Q0;PMP_PUP~P_P=PI%7IC?C?EBM:FPOPOP`GJP8CEQ0<%O4%24RI#1PZPfP:PgP;13CyR~#114~O13CKRU/0[/4OPj13C{S0<#113CJS0;/4O%9T,W>1W>T1W>S5g>5g>g01cO't=bmnPoP>1i>7PB%s>CrRmPpPq1f><R<,Lr,<qP0Pq1A<sRS/AsS0=,A@1\>N=u>CRN'L,<qS0>P01TtN,<qCKCKP?Pvb:b;b<X0>X3>%1BRT107[RM/0[=6BO14MO[[^0>^3>P8%25S0?fCRL,3CRPP2P1O4b9W2W4PBP8O2n2001000000121000000bIbJb=b7,vj13Cx10k['GPRPhPJAHCizRkPVC5P6PAPRP6PAPEPhP5O1Pw1PL5n10110000021010200RxP6PQPRPBP|P}n10110000021010300P}n10110000021010200P6PAPRPxP6PQPRfDS0@PLAHCazRxQ02C5P|P}n10110000021010300P}n101100000210102005;RXKRP6PAPRP6PAPEPJPiO1Pw1Phin10110000021010200P6PQPRPLPhAHC5z%9GRzC5P|P}n10110000021010300P}n10110000021010200,>RPhP{PkPVC5P=PkPj%2zR}9:H8P>13CaRH/0[R|1087,CC/8hXA>14BXRQ,@TA:TB\R\PTPQPT14Bb1>]TA;]TTe9QTTPYQ03PBPB%7BPXPbQ05GXERP8CEP\%92R\#9Rb#2RX,0~RQ/=O10c[R6/0[Rw=6~OS05PYPdPQPYP_P_PcO1RQO1REO1RA,0~PYPYPYPeP~P~%7~PXPAPYPYP^PbPEP_P\PQP_P2Pc%7cC?RcC?EBM:FPOPOP`GJP4CEQ05%O1%21RE#1PZPfP:PgP;%19Q07,49A`P[2ADP[2'GP4%11%2y/0[,4DP;fF,3CRy#114yOfG,3CRy?`[iADy[i'GPhfH,3C#1fI,3CRP/4OPnPoPmPpP>1As<,A@g01d;1At<C[,<qP?Pvb:b;b<X0>X3>10[BR<,08Q04/0B'G^0>^3>P8PKfK,3CO2b9WFW4PBP8O2n2001000000120000000WEW2PBP8O2n2001000000121000000bCbDb=b7bH10H<10|B'GP>10[7R|,0~Q0:/8LXA>PGP|%1|R<14|XRH'@14|wRK,@<P<PHP<PK1>]<9Q<<PYQ03P|P|%7|PXPwPYPYP^PbPwP_P\P6PcC?EBGXER%17Rw%2\Rb,47RX'@A:w76R6PwPXPwPYPQO1RX,471>]wA;]wwe9QwwPYQ03P7P7%77PbPXPYPYP^P\PQPcEBGXERPBCEP6%91R6#9Rc#2RQ,0UR\/=OADE[[=6UORXPYPdP\PYP_P_PEO1R\O1RbO1Rw,0UPYPYPYPePUPU%7UPQPwPYPYP^PcPbP_P6P\P_P1PE%7EC?C?EBM:FPOPOP`GJPGCEPX%OD%2DRX#1PZPfP:PgP;%12Q0?/0[,4210[1R2#1%2aRa?D[[7:2P4%1DQ09/0[,4jP;%1y14yO10[5R5#1%2J?D[[7:5PL%1PfJ,3C/4OPnPoPmPpPq1T@S,<qP0PqQ08P01As@Rs,Lr,<qQ0=,Ts,<q5dqCKCKP?Pvb:b;b<X0>X3>148uAD=[[9:<|\T[^0>^3>P8fE#2P{PGP9O4b9WFW4PBP8O2n2001000000121000000WEW2PBP8O2n2001000000121000000bCbDb=b7bHCYO2AD~[7P8EVb213CxP7ESWNX1>P>10l[RxA68}OXA>10xWR}/=O10I[R~,0xR{/=OPYPdP}P{PYPYPYPePxPx%7xPWP~PYPYP^PVP~P_P4PI%7IC?R4EBM:FPOPOQ06GJ%9VRW#2Rx,0lR{/=O10~[=6lOR~PYPdP{PYP_P_PIO1RIO1R{O1Rd,0lPYPYPYPePlPl%7lPxPdPYPYP^PWP{P_PVPIP4C?EBM:FPOPOP`GJPBCEP~%OG%2G#1PZPfP:PgP;%1U14UOQ0</0[10X[;6OPiQ0;#113Ch/4OPnPoPmPpPqQ0>P01AtS/LN,<qCKP?Pvb:b;b<X0>X3>10u[=68OA6uMO[^0>^3>P8PaQ0@,3CP1O3b9W2W4PBP8O2n2001000000121000000bCbDb=b7CY13CkP8ESO4ESbMW6W8W?XS3P8O1n0110101020111101P9P=P7O3PjPGO1P8ESbBb4PjP1P=PzC5PjPDP=PzC55;ReW6W8WGX5FW?X@3P8CqX@3WTWRWQWUo"). Qed.

End FPX_1.

End Frame.
