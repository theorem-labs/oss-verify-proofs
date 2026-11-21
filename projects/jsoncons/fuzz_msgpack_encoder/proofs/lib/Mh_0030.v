(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed actual_mem_is_overlay, build_stack_min_length, build_stack_starts_with_argc and 50 more; added cat_kill_no_error_run_te, cat_kill_obs_iff_te, cat_kill_omni_run_te and 21 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/CatSim.v, 935 lines within its lines 49-1665. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From Stdlib Require FunctionalExtensionality. From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence MustExit OmniEquivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module ExitSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_ExitSim () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses;reflexivityC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp7tactics<f_equal_helpC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List:firstn_nilI4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome00C4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoc59OSSVerify5KrLib7Mh_00307ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Exit9exit_specC47Corelib4Init5Logic3iffC5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch:lookup_armC5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7sa_specC4ELinuxProcessSemantics?LinuxProcessSem5Monad9unmodeledI4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I47Corelib4Init5Logic2or00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes6option00I5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7SpecArm00C5ELinuxProcessSemantics?LinuxProcessSem3Sys<SyscallTable:spec_tableC47Corelib7Classes?RelationClasses=iff_ReflexiveC47Corelib7Classes?RelationClasses9ReflexiveC45stdpp9bitvector;definitions7Z_to_bvI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedc59OSSVerify5KrLib7Mh_00307ExitSimAsyscall_spec_exitC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic5proj2I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C46Stdlib5Lists4List9app_nil_lC47Corelib4Init5Logic5proj1K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib7Mh_00307ExitSim5sim_cC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00307ExitSim7to_exit00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes3orbC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4andbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK47Corelib4Init9Datatypes6option01C46Stdlib4Bool4Bool=andb_true_iffC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC46Stdlib4Bool4Bool<orb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02k59OSSVerify5KrLib7Mh_00307ExitSim7to_exit01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01k59OSSVerify5KrLib7Mh_00307ExitSim7to_exit02C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesc59OSSVerify5KrLib7Mh_00307ExitSim>sim_c_exit_nowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00307ExitSim8sim_stepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK47Corelib4Init9Datatypes4list02I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02c59OSSVerify5KrLib7Mh_00307ExitSimBin_sysno_sys_inputC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00307ExitSimDexit_dispatch_ok_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_halted_with_haltedc59OSSVerify5KrLib7Mh_00307ExitSimAin_arg0_sys_inputC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_killed_with_haltedc59OSSVerify5KrLib7Mh_00307ExitSimJexit_dispatch_no_unmodeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelI4ELinuxProcessSemantics?LinuxProcessSem3Run4star00C46Stdlib5Lists4List9app_nil_rc59OSSVerify5KrLib7Mh_00307ExitSim9exit_postC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec00c59OSSVerify5KrLib7Mh_00307ExitSim@exit_dispatch_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep06c59OSSVerify5KrLib7Mh_00307ExitSim>sstep_exit_invC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exits_withK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun>exec_step_onlyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01c59OSSVerify5KrLib7Mh_00307ExitSim?sstep_instr_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_conseqc59OSSVerify5KrLib7Mh_00307ExitSim;to_exit_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome00C46Stdlib5Lists4List;app_eq_unitc59OSSVerify5KrLib7Mh_00307ExitSim<to_exit_execC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun9exec_starC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_realizesI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun5mexec00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun?mexec_halt_starK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome02c59OSSVerify5KrLib7Mh_00307ExitSim7on_pathC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC59OSSVerify5KrLib7Mh_00266SimInv8star_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00307ExitSim<on_path_stepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunGexits_with_never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_no_errorC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z6leb_gtK46Stdlib9micromega7EnvRing5PExpr01C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203C46Stdlib5Lists4List9app_assocC47Corelib4Init3Nat3addC47Corelib4Init3Nat3mulC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout=at_random_ptrC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout:auxv_bytesC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<string_addrsC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8word_le8C46Stdlib5Lists4List8flat_mapC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?flatten_stringsC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib5Lists7ListDef6repeatC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C46Stdlib5Lists4List:length_appc59OSSVerify5KrLib7Mh_00307ExitSimLbuild_stack_starts_with_argcC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib7Mh_00307ExitSim?word_le8_lengthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib5Lists4List>nth_error_app1c59OSSVerify5KrLib7Mh_00307ExitSimFbuild_stack_min_lengthC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02c59OSSVerify5KrLib7Mh_00307ExitSim6stm_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem3Run?entry_block_topC4ELinuxProcessSemantics?LinuxProcessSem3RunKstack_to_mem_image_in_blockC46Stdlib5Lists4List>nth_error_NoneI47Corelib7Numbers7BinNums1N00K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC46Stdlib5Lists4List6nth_okC4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_statec59OSSVerify5KrLib7Mh_00307ExitSimBoverlay_argc_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01c59OSSVerify5KrLib7Mh_00307ExitSim;init_first8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula02C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto4kind02C46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc59OSSVerify5KrLib7Mh_00307ExitSimAmachine_state_etaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00307ExitSimEactual_mem_is_overlayC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00307ExitSim:enum_stateC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelc59OSSVerify5KrLib7Mh_00307ExitSim=sim_c_to_exitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun8omni_runI4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun8is_errorc59OSSVerify5KrLib7Mh_00307ExitSim=exit_omni_runC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<exec_obs_iffC4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit>must_exit_withC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalenceBmust_exit_with_iffI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exec_soundC56Stdlib6ZArith6BinInt1Z4landC45stdpp9bitvector;definitionsCbv_and_obligation_1C47Corelib7Classes?RelationClasses?Equivalence_PERC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<img_segmentsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:omni_corunC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence:omni_equivC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_coexecC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunDnever_errors_coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=coexec_conseqC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence@omni_trace_equivC4ELinuxProcessSemantics?LinuxProcessSem3Run3runC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalenceDtrace_equiv_iff_omniC4ELinuxProcessSemantics?LinuxProcessSem3Run9obs_tracec59OSSVerify5KrLib7Mh_00307ExitSim<exit_obs_iffC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=bh_errors_iffc59OSSVerify5KrLib7Mh_00307ExitSimAexit_no_error_runC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6errorsC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence7modeledC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence5equivC59OSSVerify5KrLib7Mh_00266SimInvDno_error_run_modeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=bh_all_errors".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_exit_no (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Lemma syscall_spec_exit : forall i m o,
  is_exit_no (in_sysno i) ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) [] "p'0h01Eh11Hh21ih31mh41oh51zi001ai011xp;1p;2p;3p;4p;6p-1R0p10000p4p710R1p9P0g000SR2p4p710R3p9P0p1001AR4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p1001_p4p710R4p9P0p1002Wp4p710p8p10037p4p70R0p1003gp4p710R5p8P0p1004Cp4p710R6p8P0p1004ap4p7210R7p8P0g005>R0p4p710R8p8p1005\p4p710R9P5p8P9P8p8p10069p4p70R:p1006gp4p7210p8P:P5p8P:P9p8P:P6p8P:P7p8P:P8p8P:p1007Cp4p710p8p1007`p4p7210R:P1p8P:P3p8P:P5p8P:P6p8P:P7p8P:p1008Lp4p7210p8P:P8p8P:P4p8p1008ip4p70R4P5p8P4P6p8P4P7p8P4P8p8p1009_p4p710R4P5p8P4P8p8g00:>j1ATg00;6j13Tg00;mj1;Tg00<lj10Tg00=Qj1@Tg00=oj27Tg00>Yj11Tg00?>j19Tg00?\j32Tg00@6j38Tg00A1j24Tg00Afj46Tg00BhR8j25Tg00CAj2?Tg00DAj4>Tg00E>j4=TP2j4<TP0j6:Tg00F6g00G3g00GiR0#Af2R2#3#;g00Hgg00IAR4g00I_#0R5#0#0#0#0#0#@R7f3R6#3'7R:%15#1#1R5#0#1#9R332%15#0#9R5924:f4R:?862g00JDR1,4:P:P6P2C6'5f0R2%3:,77R9=243P4P3g00Jcg00KEp-0R3g00LD/?2P2f7f6R;f5R<C>P0P;P<P:C=n1011010002101000014;1P;P<P:C6'5X54R;P3P8g00MH14<1P<P:P6C6R1C<R8%3<,77R7P2E:A8<:6/51R1eW0P2O1A2495P4P5P;P8P7P2E:P1eW0P2O1n200100000021000010000W1W4W3W2o"). Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok : forall i m,
  is_exit_no (in_sysno i) ->
  syscall_spec i m
    (Ok (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []).
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) [] "h04evs2h14evs1h22m1h33Hnoh41ih51mh61xp;1p;2p;6p;3p;4p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0p1003gp4p710R4p8P0p1004Cp4p710R5p8P0p1004ap4p7210R6p8P0p1005>p4p710R0p8p1005\p4p710R7P4p8P7P0p8p10069p4p70R8p1006gp4p7210p8P8P4p8P8P7p8P8P5p8P8P6p8P8P0p8P8g007CR8p4p710p8p1007`p4p7210R7P1p8P7P2p8P7P4p8P7P5p8P7P6p8P7p1008Lp4p7210p8P7P0p8P7P3p8p1008ip4p70R3P4p8P3P5p8P3P6p8P3P0p8p1009_p4p710R3P4p8P3P0p8g00;6j1NTg00;mj1MTg00<lj16Tg00=Qj1@Tg00Ndj2HTg00OJj1ETg00Omj1DTg00PMj2=Tg00Pmj19Tg00QMj6KTg00A1j27Tg00>Yj14Tg00?>j1ITg00RKj3:Tg00S0j28Tg00@6j3GTg00Afj4FTg00Sjj4LTg00:>j1CTg00U0j4>TP8j3?Tg00?\j35Tg00Uhj23Tg00VBj2BTg00V]j2<Tg00W7j4ATg00WRj4;Tg00Wlj4JTg00GiR8f2R0f1R3f0R4C>p=0g00XGR6g00XgR5P3P4C>p=2f3R7?503/B4p=1g00F6g00G3R2%N3#Mg00I_R1#6#6#6R9#6#6#6#@R:g00YG'H%E:R;%@9#E#D'=#91=;;#9R9P9g00Ye#9g00Z],=;#9EKR;g00JDR9,70R<%41#4#4#4#4#4#4#I,H:R15::/83R=g00[<R>#9R?30R@9G031779RAP7P0A::A1/80RA=0;?RBCF[P<P0P3P@CFR<AG70B[P0P3P@P4CLP6%D>RC%C6RDP6P7P0P3C>f6/79=::1f5RE'8RF/2?%C8R8A0;F4A0;0?RFA?>3495C?RGC1C1X0C,3CX1C'3X22,32X66RHP5P2PD120317E9=::1f4RE'8R0/2?P8A0;04PFPGC1C1X0C,3CX1C,3CX22P=PCPD17E9=::1/87R7/23127?P8A0;74A0;7?PGC1C1X0C,3CX1CP?PCPD12A?RGPGP8A0;A4PBA?>?495C?C1C1X0CP?12=?R==5D=A58@@R4A?>??R>95C?R?'B1<D=P4P?1<8@1<C>CACAC;C;C;C;136HeP<eCJW3W5W4o"). Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok_inv : forall i m eff m' evs,
  is_exit_no (in_sysno i) ->
  syscall_spec i m (Ok eff m' evs) ->
  eff = mkEffect (Z_to_bv 64 0) [] [] /\
  m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m /\ evs = [].
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) [] "p'0h04evs2h12H3h21eh31Hh42H0h52H1h62H2h74evs1h82H4h91lh:1mi001mh;2m1h<2H5h=5Hspech>3evsi013evsh?1oi021oh@1xi031xhA2x2hB2H6hC3HnohD3effhE1ihF2m'hG1shH1uhI2x0hJ2x1p;1p;3p;4p;2p;6p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0p1003gp4p710R4p8P0g004aR5p4p710R6p8P0P5p4p7210R7p8P0g005>R0p4p710R8p8g00\2R9p4p710R:P4p8P:P8p8p10069p4p70R;p1006gp4p7210p8P;P4p8P;P:p8P;P6p8P;P7p8P;P8p8P;g007CR;p4p710p8p1007`p4p7210R:P1p8P:P2p8P:P4p8P:P6p8P:P7p8P:p1008Lp4p7210p8P:P8p8P:P3p8p1008ip4p70R3P4p8P3P6p8P3P7p8P3P8p8p1009_p4p710R3P4p8P3P8p8g00Omj1WTg00;6j1`Tg00;mj1[Tg00@6j3NTg00Afj4STg00Sjj4ZTg00\Pj4YTg00:>R8j1RTg00<lj1@Tg00=Qj1OTg00>Yj1>Tg00?>j1^Tg00Ndj2VTg00Pmj1BTg00OJj1TTg00PMj2KTg00QMj6\Tg00?\R3j30Tg00UhR4j24TP5j6ATg00VBR5j27Tg00V]j2CTg00W7j4XTP9j2_TP0j68Tg00U0j4=Tg00A1j2ETg00RKj3ITg00S0j2MTP;j3]Tg00GiR;f2R0f1R9f0R7C=p=1g00JDR6,E7p=Ug00XGR:P0P9P7C=p=5P:g00XgR2f4R1f3R</E6;I0/M9P7C=p=9g00[<R=?]97p=3f6R>f5R?;01A0<09/77'7p=;1E06=I<9/M7p=2A0;>?g00G3R@?01<A0097'7'7p=:P:P2P9P7C=p=?P:P<P0P9C==017p=HP;P1P<P0C==0?9/77p=QP;P<P0P9C==017p=GA0@97p=6A0;97p=DA0097,7<,71p=<1797,70p=PA0:72p=F1E96=I07p=J1M9790@0p=Lg00F6%W=R6%`1#[A1<099N?1A11<0RA9N>?f7RB#UPBP>A1?1<RCCS[%U>P>P?PACSRDANB>C[P>P?PAP9CZP7CYPDP4P:%R:RDA5<09RAg00I_RC#@#@#@RE#@#@#@#ORFf;RG%>C#>#>#>#>#>#>#^,VFRCf:RH%B=RID9%R;RJf9RKf8RL;17g00YG,VF%TFRM%OE#T#W'K#B1KMM#BREPEg00Ye#Bg00Z],KM#BE\RM?10IRE1397RN906BF;X06,46X76,46X;@,4@X@:P>PMP?PFPLPCPBC2P6P1PIF:P7PDPAPFf=RAPCf<ROPID9PJA1GH7PEA06KNF;X06,46X76,46X;@,4@P4P@PDA5109PFf>RPPCPAPID9PJA1OG7PEA06HNF;X06,46X76,46X;@PHPMPKPFPOPCPGC2P6PLPIF:P7PDA5>09PFf@RQPCf?RRC2RS/?IPJA1PA7PEA06ONF;X06,46X76,46P4P6PDA5B<9PFfAREPCPQPID9PJA1RP7A1M<IA06ANF;X06,46X76PPPMPAPSP6POPIF:P7PDA5K?9PFfCRSPCfBRPPID9PJA1EQ7A1M?IA06RNF;X06,46P4P6PDA5H>0PFfDR4PCPSC2RN/?IPJA1PE7A1M>I1307906QF;X06PPPMPEPNP6PQPIF:P7PDA5OL1PFfFRNPCfER>PID9PJA14S7A1MLI1317906PF;P5PDPAPKP?PFfGR<PCPNPID9DHPJP>P4P9A1MKI13?9906SEQPNPMP>PFfHRTPCP<C2P6P4PIF:P7PDPRPGPBPFfIRUPCPTPID9DHPJPTP<P1A1MOI13L1906NEQP5PJPUPTP?A1MAIDG13K?906<fJR<PMPUPFfLR?PCfKR5C2P6PTPIF:P7PJP5P<PBA1MRIDG13OL906<P3PJfMRL?1?KRKA1MSIRR90J9fPRBPMfORNPFfRR1PCfQRVC2P6fNRWPIF:[P9A1MEIRE90JKPJPWPLPHA1MPIRHDGPJP6P8P;P6P7P7POn10110200023010310010100X2JA1NWGPRP7EAA06GIPJP@P8P;P@P7P9PBn10110200023010310010100X2JA1BNOA1M4IP9EA16N4PJP;P8P;P;P7P0P1n10110200023010310010100X2JA1VBAA1M>IP0EA1DVM1D1MP7fSR>/DMP;PMfTRA/6UROA06PIRPP0PMfVRRPFfYRKPCfXC2P6fURXPIF:[[XG;16>TP7POP@P<A06SIRS1DMMROPFfZRYPCPKC2RK,69P6PRPID<[X:@P7PSP6PIPOPFf[RSPCPYC2RY,6LRZP6fWR[PID<X96P613T4A067IR\9POZX>6P6PIPOPZP613U7PID<XA6P3PDA5B?TRTPFf\R3PCPSC2RS/?IRZ90D9POPFf]R]PCP3C2R3,6NR^P6135IPID<[PQ1?KIRK90DTPDPVPLPU1?YIRYDHPDP6P8P:P6P7P7P5n10110200023010310010100X2DA51W<PZP7EAA06<IPDP@P8P:P@P7P9PBn10110200023010310010100X2DA5>N51?3IP9EAP^PDP:P8P:P:P7P0PXn10110200023010310010100X2DA5AB?PFf^PCP]PID9P0EA%FA%FXP7%FRP:P2fbR2=JFCfaR05LAR]A06VIR?POfdR8=JFCfcR^5LRP6131IPID<[[XH:AJF0Cf`5L>P7P]P@PFP^PCP2C2A061IR1POPFfeR2PCP8C2R8,69P613>IPID<[X:@P7P1P6PIPOPFffPCP2C2R2/62R2P6137IPID<X96P6PIAPO2\X96PO1688R2A06IIR\'71C;MP2P\1C@81C6ICXCX13II1_=IE8P>P7E8b8X1?PXP7E8b1W6P[P7E8b6W5P7O1b5P7O1b5P7O1b5W4P7O1W4n2002102000010101A0D7YPO16WSP613<IPID<[X?DPKO1P71CDYO1b4P4P9E8PRPGE8P4P7E8bBX<PPXP7E8b<W8PAP7E8b8W1P7O1b1P7O1b1P7O1b1W6P7O1W6n2002102000010101A0J7HPNPMPWPFPVPCPBC2P6PLPIF:[X?JPEO1P71CJHO1b6W5W4P9P7O2n2001000000121000000W4W3P9P7O2n2001000000121000000W3XA6P9P7O2n2001000000121103000W3XJ6P9P7O2n2001000000121103000W3XI@P9P7O2n2001000000121103000W3X@:P9P7O2n2001000000121103000b=W=WCW>XF@XD;X:@WEo"). Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_no_unmodeled : forall i m,
  is_exit_no (in_sysno i) -> ~ syscall_spec i m Unmodeled.
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) [] "p'0h01Hh14evs1h21eh32m1h42H0h52H2h61xi001xh72H1h82H3h92H4h:5Hspech;1mi011mh<2x0h=2H5h>3Hnoh?1ih@1lhA1oi021ohB1uhC2x1i033evsp;1p;3p;4p;2p;6p;7p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0g003gR4p4p710R5p8P0g004aR6p4p710R7p8P0P6p4p7210R8p8P0g005>R0p4p710R9p8p1005\p4p710R:P5p8P:P9p8p10069p4p70R;p1006gp4p7210p8P;P5p8P;P:p8P;P7p8P;P8p8P;P9p8P;p1007Cp4p710p8p1007`p4p7210R;P1p8P;P2p8P;P5p8P;P7p8P;P8p8P;p1008Lp4p7210p8P;P9p8P;P3p8p1008ip4p70R3P5p8P3P7p8P3P8p8P3P9p8p1009_p4p710R3P5p8P3P9p8g00;6j1YTg00;mj1XTg00\kj1GTg00@6j3?Tg00Afj4JTg00Sjj4UTg00\Pj4STg00:>R9j1FTg00<lj17Tg00=Qj1DTg00>Yj16Tg00?>j1MTg00Ndj2KTg00Pmj1:Tg00Omj1ITg00OJj1HTg00PMj2CTg00QMj6TTg00?\R3j30Tg00UhR5j21TP4j6ETg00]cj2RTP6j6ATP0j7Oj6BTg00V]j2NTg00^Bj1QTg00A1j2>Tg00RKj3<Tg00S0j2;Tg00U0j48Tg00VBR0j2WTf0R6g00JDR4'>p=Lf3R8f2R7f1R;3</;6p=Vg00XGR2g00XgR1P;P6C89087p==P2P7P;P6C8p=2g00GiR:P7P;P6C8p=4f7R<f6R=P2P1f5R>f4R?/>4;<8/;7P;C830/W6p=51>74=<8;/;6p=3P2P11>84=<?7/;;P6C8p=9P2P1P;P6C8p=PA0261p=@g00F6g00G3R4%Y;#X%G:R@9?7;RAA?87@%L?RBP?P8P@CJ[%L8P8P7P@CJRCA??8@[P8P7P@P;CUP6CSPCg00Hg%F2RC%G2RDg00I_RE#7#7#7RF#7#7#7#DRGPB%6E#6#6#6#6#6#6#M,KGREP8CVg00[<RB#:RHC=%IBRBPCA27;6RIPGP<PEP=PH%F:RJg00YG,KG%HGRK%DF#H#I'C#:1CKK#:RFPFg00Ye#:g00Z],CK#:ETRK?4;H70@RFG5X1B'1X34,14X62,12g00^[RLP6PCPDPGP>PEP?C3PHC=PCPDP9P2p-0RDP6PLg00_8RMn10110200023010010110300X2Cg00_TRNPGP=PEP>PHD9P6EEPL1RL6ROb4W0P6O1PCPIPGf8RPPEP<PHPFG5X1B,1BX34,14X62,12P5P2PCPIPGf9RQPEPPPHPFG5X1B,1BX34,14X62PLP6PCPIPGf;RIPEf:RRPHPFG5X1B,1BX34,14P5P4PCA28;6PGf<RSPEPIPHPFG5X1B,1BX34PLP6PCA2>;6PGf>RTPEf=RUPHPFG5X1B,1BP5PBPCA2=76PGf?R5PEPTPHA4K7H90J@G5X1BPLP6PCA2P?6PGfARFPEf@RVPHA4K?H90J@G5P0PCA2Q>;PGfBR0PEPFC3PHC=A4K>H90J@PLP6PCA2I<8PGfDR?PEfCRWC3PHC=A4KPH90J@P3PCA2UQ>R>PGfHR3PEfGRXPHD9RY90C;PL[P;PGfFRZPEfEPHD9R[90C>A2TR=PGPXPEPZPHD9RZ50CPCPBP9P2PBP6P6PPn10110200023010010110300X2CA25I<PYP6EAA0B<HPCP4P9P2P4P6P;PUn10110200023010010110300X2CA2VSPPGfIRPPEP3C3R3/PHP;EAA04S3PCP2P9P2P2P6P7P0n10110200023010010110300X2CA2FUQPGfJPEPPPHD9P7EA%@F%@0P6%@WP2P1PGfNR1PEfMRWC3904FRFA0BTHRTPL[[XB2PGPWPEfLC3904VP6PFP4PGfOPEP1C3A0B5HR5PL[X;4P6P5PBPHPLX@BP4PGfQR5PEfPC3R1A4K6H90J@PL]4X<4A4K1H90J@PJP@P9P:PDP6PLPMn10110200023010010110300X2JPNPGfRPEP5C3=4KHP6EEPLPOb0W4P?P8PIFOPVP6EBb=X9TP0P6EBb9W8P?P6EBb8W5P6O1b5P6O1b5P6O1b5W7P6O1W7n2002102000000101A0C6ZPL[XACP[O1P61NCZO1b7W4W0P;P6O2n2001000000121000000W0XCBP;P6O2n2001000000121100000W0X<4P;P6O2n2001000000121100000W0X62P;P6O2n2001000000121100000W0P6O1n200100000021000011000b:W:%QAeW>W;W?o"). Qed.

(* [comment removed for export] *)
Lemma in_arg0_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) [] "h02msh14segsh22x8p;1p;2p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0p1003gp4p710R4p8P0p1004Cp4p710R5p8P0p1004ap4p7210R6p8P0p1005>p4p710R0p8p1005\p4p710R7P4p8P7P0p8p10069p4p70R8p1006gp4p7210p8P8P4p8P8P7p8P8P5p8P8P6p8P8P0p8P8p1007Cp4p710p8p1007`p4p7210R8P1p8P8P2p8P8P4p8P8P5p8P8P6p8P8p1008Lp4p7210p8P8P0p8P8P3p8P8p100`0p4p710p8p1008ip4p70R8P4p8P8P5p8P8P6p8P8P0p8p1009_p4p710R8P4p8P8P0p8g00Omj15Tg00<lj10Tg00=Qj12Tg00OJj11Tg00a:j24Tg00V]j23Tg00b8#5g00c7g00I_#0#0#0#0#0#0#2#1R0f1g00JD'4,30W2W0W1o"). Qed.

(* [comment removed for export] *)
Lemma in_sysno_sys_input : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) [] "h02msh14segsh22x8p;1p;2p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0p1003gp4p710R4p8P0p1004Cp4p710R5p8P0p1004ap4p7210R6p8P0p1005>p4p710R0p8p1005\p4p710R7P4p8P7P0p8p10069p4p70R8p1006gp4p7210p8P8P4p8P8P7p8P8P5p8P8P6p8P8P0p8P8p1007Cp4p710p8p1007`p4p7210R8P1p8P8P2p8P8P4p8P8P5p8P8P6p8P8p1008Lp4p7210p8P8P0p8P8P3p8P8p100`0p4p710p8p1008ip4p70R8P4p8P8P5p8P8P6p8P8P0p8p1009_p4p710R8P4p8P8P0p8g00Omj14Tg00<lj10Tg00=Qj12Tg00OJj11Tg00V]j23Tg00b8#4g00c7g00I_#0#0#0#0#0#0#2#1R0f0,30W2W0W1o"). Qed.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable code : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    ms_gpr ms 0 = code ->
    to_exit ms
| te_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_exit ms' ->
    to_exit ms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint sim_c (fuel : nat) (ms : machine_state) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match ms_svc_pending ms with
    | Some x8 => ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
                 && bv_eqb (ms_gpr ms 0) code
    | None =>
      match RiscvSemantics.step segs ms with
      | MachineOk ms' => sim_c fuel' ms'
      | MachineFault | MachineUnmodeled => false
      end
    end
  end.

Lemma sim_c_to_exit : forall fuel ms, sim_c fuel ms = true -> to_exit ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) ["WithSegs"] "p'0h01Hh12H0h25Hsteph34Hsvch42b1h52b2h64fuelh71mi001mh82msh94Hgprh:3Hx8h;1ah<1bi011bh=1nh>2IHh?1eh@3ms'i023ms'hA1oi031ohB2x8i042x8i056resulti061xp;2p;1p;6p;3p;5p;4p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0g003gR4p4p710R5p8P0p1004Cp4p710R6p8P0p1004ap4p7210R7p8P0p1005>p4p710R0p8p1005\p4p710R8P5p8P8P0p8p10069p4p70R9p1006gp4p7210p8P9P5p8P9P8p8P9P6p8P9P7p8P9P0p8P9p1007Cp4p710p8p1007`p4p7210R9P1p8P9P2p8P9P5p8P9P6p8P9P7p8P9p1008Lp4p7210p8P9P0p8P9P3p8P9p100`0p4p710p8p1008ip4p70R9P5p8P9P6p8P9P7p8P9P0p8p1009_p4p710R9P5p8P9P0p8g00d>j24Tg00e8j1=TP4j6ATg00]cj2DTg00f6j1WTg00fUj1:Tg00<lj15Tg00=Qj1RTg00OJj1JTg00JcR4j1HTg00V]j2BTg00?\j32Tg00=oj23Tg00>Yj1<Tg00?>j1CTg00g[j21Tg00h8j27Tg00a:j2;Tg00hUj38Tg00iBj2@Tg00i`j29Tg00j\j2VTg00VBR0j2?Tg00k>j2UTg00k_j3QTg00HgR9j2>Tg00lTj2NTg00;mj1ITg00m4j2KTg00mTj3GTg00mnj3LTg00nHj5MTg00oFj1FTg00ohR5j1OTg0110j2PTg0128j5ETg0136j1STg014>j1TTg015Fj4XTg015gR7f0R6g016GR332p=0g00IAR2f1R1;26p=6g00Z]R8g00c7R:1416#0%=1[]8R;X68g00JDR</46#0P714<1P7p-0P6g00^[R=g00_8n0110100020000X?7R>g00_TR?P3P6EAP=f2R@#=/D6b1W0X8:%W@/46#0%:1g00I_#5RA#5#5#5#5#5#RRB#JRC#HRD1BD6%:@=2D6P4PCf4RE#:=2D6P4PCP7P113B6R4%<A#<#<RA#5#<#CRF'1%<A#5#CRA,14'7f6R4/;<p,4codeRG58BRH'@P5P:P7p,4segsRIf5RJ'9RKf8RL/46g016gRMPMn1011060003101020000n10110600021010400#0%=4]0]3P1%:J1VC652D13B1RJ/1F11JA'7/@H#0P01@16#0%0@RH%01RJ'?[RN%06RO,?J1@@1#0RP[f3RQ#0RR/?H\P1U16P1n2001000000120000000X57X47PN^57^47P613BQRN/1F11NA'7RN1;L<=8BGRPP1O3%0N%0P'?P013BERP/1F11PA'7#0f9RP/;<=8BG#0f:RN#=RSP613B4RT/1F11TA'7#0f<RT/;<=8BG#0P0A8B16#0A2C@1[RUA2C16A8B@1#0RV[A2CQ@\VAQB16P1n2001000000120000000X<CX;CPU^<C^;CP6f>/;<R<PGP1O3A2C<Gf?R<PNPPP01716#01>HJ[RN1>JO17@1#0RO[1>RH\O1N16P1n2001000000120000000X57X47PN^57^47P6f;RN,3BRO/1FRR11OAROPEO3%0R%0O'>P913BTR9/1F#0119A#0f=R9#IP613B9R9/1F#0P01116#016@1[R0161611@1#0RO[16Q@\O1K16P1n2001000000120000000X72X=2ROP0^72^=2R2P613B<R<PFP1O316<Ff@,3BRB/6FRF16BARB;G6b0b1W0P6O1119A#0POP2P6P<PAP1O316<AALFB6b0b1W0P6O1n200100000021000010000b:b0P6DMb9b0W9W:P1P6O2n2001000000121000000b0b1W0W3XBCP6O1%:Q%FC52DP5P:P719IEf7RE/46PMPMn1011060003101020000#0PK%O:RK1BK619I4=2K6P5P:19IL=2K6P5P:P7P114T6PMPMn1011060003101020000#0PS]0]2P119IP1P:652K14T1#0PNP@PEP1PTP@P6O2DEW0W2X@:P6O119IERE%S:52KA27M3P7PMP>P?P3P6EAP=1DS6b1W0RSW2%T:92KEPSW2n1011000003101050000P6P@O2b2b7W0W3n10110300021110100P6P@O2b3bAW0X8:X>;X68P6CXW6o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sim_step : forall fuel ms ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sim_c fuel ms' = true ->
  sim_c (S fuel) ms = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) ["WithSegs"] "p'0h04Hrech15Hsteph24Hsvch34fuelh41mh52msh63ms'i003ms'h71oi011xi022x8p;1p;3p;2p;6p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0p1003gp4p710R4p8P0p1004Cp4p710R5p8P0p1004ap4p7210R6p8P0g005>R0p4p710R7p8p1005\p4p710R8P4p8P8P7p8p10069p4p70R9p1006gp4p7210p8P9P4p8P9P8p8P9P5p8P9P6p8P9P7p8P9p1007Cp4p710p8p1007`p4p7210R9P1p8P9P2p8P9P4p8P9P5p8P9P6p8P9p1008Lp4p7210p8P9P7p8P9P3p8P9p100`0p4p710p8p1008ip4p70R9P4p8P9P5p8P9P6p8P9P7p8p1009_p4p710R9P4p8P9P7p8g00<lj10Tg00=Qj1ETg00OJj1>Tg00JcR7j1<Tg00fUj1:Tg00oFj1DTg00?\j35Tg00ohR9j1=Tg00i`j24Tg0110j27Tg00d>j23Tg00=oj2;Tg00>Yj11Tg00?>j19Tg00g[j26Tg00h8j2CTg00a:j2BTg00hUj3@Tg00iBj2?TP0j68Tg00f6j1ATg015gR0f0R4g016G35p=2g00Z]g00c7R6g00I_#0R5#0#0#0#0#0#ER3#>R2#<R1f1R8#:%D2R:35%=6R;p,4segsR<f2R='4176835f4R>/3=#2P1P:P7P2P0P41;34R2%15#1#1R5#0#1#9'6%15#0#9,62'Cf6R2g00JD'Bp,4code5@3'?P9P6P0f5R3,4<f7/34R5g016gR7P7n1011010003101000000n10110100021010200#2X71P;f3,76P9P6P0P4P5P7P7n1011010003101000000#2X4;P414<>R<P8E8P9P6P0P<1324P7P7n1011010003101000000#2e%:>P=E8%A3/3>#2eW0W1W2X66W5W3o"). Qed.

(* [comment removed for export] *)
Lemma sim_c_exit_now : forall fuel ms x8,
  ms_svc_pending ms = Some x8 ->
  ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z) = true ->
  bv_eqb (ms_gpr ms 0) code = true ->
  sim_c (S fuel) ms = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) ["WithSegs"] "p'0h05Hcodeh14Hsvch23Hx8h31bh44fuelh52msh61oh72x8i002x8i013ms'i021xp;1p;2p;3p;6p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0p1003gp4p710R4p8P0p1004Cp4p710R5p8P0p1004ap4p7210R6p8P0g005>R0p4p710R7p8p1005\p4p710R8P4p8P8P7p8p10069p4p70R9p1006gp4p7210p8P9P4p8P9P8p8P9P5p8P9P6p8P9P7p8P9p1007Cp4p710p8p1007`p4p7210R9P1p8P9P2p8P9P4p8P9P5p8P9P6p8P9p1008Lp4p7210p8P9P7p8P9P3p8P9p100`0p4p710p8p1008ip4p70R9P4p8P9P5p8P9P6p8P9P7p8p1009_p4p710R9P4p8P9P7p8g00<lj10Tg00=Qj1CTg00OJj1@Tg00JcR7j1?Tg00fUj1>Tg00j\j2<Tg00?\j3;Tg00=oj28Tg00>Yj13Tg00?>j1:Tg00g[j22Tg00h8j27Tg00a:j26Tg00hUj35Tg00iBj24Tg00i`j2BTg00d>j29TP0j6=Tg00f6j1ATg015gR0f0R9g016GR43;p=1g00Z]g00c7R6g00I_#0R5#0#0#0#0#0#CR3#@R2%?2R1f1R8#>1<293;1838R:%35#3#3R5#0#3#:R;'2%35#0#:R5,2:'7#1f3R:g00JDR<'6p,4codeR=553#1P11<2:P7P2P0P91839R2/2;1225'7f6/6<=53='4g00ohP6P0p,4segsf5R6'Bf7/99g016gR2P2n1011020003101010000n10110200021010000#1X61P0P4166<=53=,49#1X30P9f4R9/6<=53=R=,44#1e183:R:/2;12:5'7R:P8E=14:=#1e%>9f2E=%A6/99#1eW0W2W1W7W5W4o"). Qed.

(* [comment removed for export] *)
Lemma sim_ecall_exit : forall fuel ms,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some 0x73 ->
  ((bv_unsigned (ms_reg ms 17) =? 93)%Z || (bv_unsigned (ms_reg ms 17) =? 94)%Z) = true ->
  bv_eqb (ms_gpr ms 0) code = true ->
  sim_c (S (S fuel)) ms = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) ["WithSegs"] "p'0h06Hcheckh15Hcodeh26Hfetchh34Hsvch44fuelh52msh63ms1h71oi003st'i011wi021xp;1p;3p;2p;8p;6p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0p1003gp4p710R4p8P0p1004Cp4p710R5p8P0p1004ap4p7210R6p8P0g005>R0p4p710R7p8p1005\p4p710R8P4p8P8P7p8p10069p4p70R9p1006gp4p7210p8P9P4p8P9P8p8P9P5p8P9P6p8P9P7p8P9p1007Cp4p710p8p1007`p4p7210R9P1p8P9P2p8P9P4p8P9P5p8P9P6p8P9p1008Lp4p7210p8P9P7p8P9P3p8P9g00`0R9p4p710p8p1008ip4p70R3P4p8P3P5p8P3P6p8P3P7p8p1009_p4p710R3P4p8P3P7p8g00<lj10Tg00=Qj19Tg00OJj1?Tg00JcR7j1;Tg00fUj1\Tg00oFj1VTg00?\j32Tg017Gj17Tg018Dj2<Tg00>Yj11Tg00?>j13Tg019Fj3GTg00j\j26Tg019ij2:Tg00=oj2YTg00g[j2HTg00h8j2UTg00a:j2TTg00hUj3STg01:gj1DTg01;fj1CTg01<fj1BTg01=gj1ATg01>fj1@Tg01?ej15Tg01@cj1ETg01Aaj8FTg00f6j1PTg00ohR3j1>Tg01Bhj1OTg01Coj3=Tg01E;j3MTg01F@j3LTg01GFj3NTg00Pmj1KTg01HKj3QTg0110j24Tg0136j1JTg014>j1RTP9j28Tg00V]j2ITP0j6[Tg01IRj2ZTg01JWj6XTg01KZj6WTg00Z]g00c7R0g00I_R9#0R4#0#0R6#0#0R5#0#9R2#?R1#;R8f0R:#\%V132%95R5#?R;#;R<p,4segsR=f1R>#7'<%19#1#0#0#1#1#3g00_TR95G5R5,6;R?32g015gR@f2RA%14R4#9%16#3;G9R9':,Y2R6%14#1R4#0#1#3'H%14#0#3,H6'Ug016GR632f3R4g00JD'Tp,4code5S2=2@6f4R6#D%C6%B61:69,61%A6%@6%56%E6GFP0f6R@#Pf5R2P:P6P<P?%>0R?P7P;%O0R6#>RBP:f7===:RCP7P;PB%5@RD%7@RE5M=PCP7P;PBAL=DEPCP3P0PBAN=DEg01LW#K9Q0:,46%J6%R6n1011020003101000000n10110200021010100n10110200021010100n10110200021010100,80140>32X7<%D2%C2%B21:29R9,61R1%A2%@2%52%E2GF,40,I?A==25,80140:R552?e%72,<=P4E[1Z=2,80=2?5eP@P:P91I81PAP>EXEWb6W1W0W2W3W5W4o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_instr_inv : forall ms model ms' evs st,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
  intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
  inversion Hss; subst.
  - (* sstep_instr *)
    match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; inversion H; subst end.
    split; reflexivity.
  - (* sstep_instr_fault *)
    match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_instr_unmodeled *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_call: its first premise is the same [MachineUnmodeled] *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_materialization_fault *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_unmodeled *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_syscall *) congruence.
  - (* sstep_syscall_materialization_fault *) congruence.
  - (* sstep_exit *) congruence.
  - (* sstep_killed *) congruence.
  - (* sstep_syscall_unmodeled *) congruence.
Qed.

(* [comment removed for export] *)
Lemma sstep_exit_inv : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)] /\
  st = SNext (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
Proof.
  intros ms model x8 evs st Hh Hsvc Hexit Hss.
  inversion Hss; subst; try congruence.
  (* Five arms survive, all carrying ms_svc_pending _ = Some _.  Rebuild the
     is_exit_no fact per goal from the arm's OWN syscall input.  Nothing below
     may name ms / model / segs / x8: `inversion ...; subst` renames and clears
     the statement's binders (measured -- a build round failed
     with "The reference ms was not found" at exactly such a pattern), so every
     pattern here binds what it needs instead. *)
  all: match goal with
       | Hsp : syscall_spec ?i _ _ |- _ =>
           assert (Hy : is_exit_no (in_sysno i))
             by (rewrite in_sysno_sys_input;
                 match goal with
                 | He : is_exit_no ?z |- is_exit_no ?y =>
                     replace y with z by congruence; exact He
                 end)
       end.
  (* exit_dispatch_no_unmodeled yields a term of type False, and the goal here
     is the conjunction, so `exact` would be ill-typed; destructing the False
     closes any goal.  Measured: with `exact` this whole match reported "No
     matching clauses for match" (a build round),
     because a clause whose BODY fails makes Ltac fall through to the next
     clause and then report no clause matched -- the error names the match, not
     the ill-typed term inside it. *)
  all: match goal with
       | Hsp : syscall_spec _ _ Unmodeled, Hy : is_exit_no _ |- _ =>
           destruct (exit_dispatch_no_unmodeled _ _ Hy Hsp)
       | Hsp : syscall_spec _ _ (Ok _ _ _), Hy : is_exit_no _ |- _ =>
           let E := fresh "E" in
           pose proof (exit_dispatch_ok_inv _ _ _ _ _ Hy Hsp) as E;
           destruct E as (E1 & E2 & E3); subst
       end.
  all: rewrite ?in_arg0_sys_input in *.
  all: autorewrite with model in *.
  all: try discriminate.
  (* only sstep_exit is left *)
  all: match goal with
       | H : Some _ = Some _ |- _ => injection H as H; subst
       end.
  all: cbn [app]; split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma star_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star segs c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hst.
  destruct Hst as [ c0 | c1 evs0 c2 tr0 c3 Hss Hrest ].
  - split; reflexivity.
  - exfalso. inversion Hss; subst; cbn [cfg_model] in *; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition exit_post (fs : Fs.Fs) : post :=
  fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
              /\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.

Lemma to_exit_exec : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  OmniRun.exec segs (mkCfg ms model) (exit_post (m_fs model)).
Proof.
  (* Ported by name from the model's own proof at
     727298f3:theories/Common/ExitSim.v:366-404.  The recorded KReplay term
     this replaces applied [sstep]'s exit constructor positionally, and
     727298f3 inserted three vDSO arms ahead of it ([sstep_vdso_call],
     [sstep_vdso_materialization_fault], [sstep_vdso_unmodeled]), so the
     replay reached [sstep_vdso_unmodeled] with a [word] where a [VdsoFn]
     was expected (a build round).  The
     statement is unchanged. *)
  intros ms model Hh Hlazy Hte.
  induction Hte as [ms x8 Hsvc Hx8 Hgpr | ms ms' Hsvc Hstep Hte IH].
  - (* te_here: the one transition is the exit, into the halted configuration *)
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
    + intros evs st Hss. exact (sstep_exit_inv ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold exit_post. cbn beta. rewrite app_nil_r, Hgpr. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* te_step: one silent instruction *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact IH |]. intros tr o H. cbn [app]. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_exit_star_only : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    tr = [] \/ tr = [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)].
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) ["WithSegs"] "p'0h01oh11Hh23Heqh35Hstarh42trh52_Hh63tr'h72HQh82Hhh95Hlazyh:3Hteh;1ch<1eh=5modelh>2msh?2o0i001xp;1p;3p;2p;4p;5p;7p;8p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0p1003gp4p710R4p8P0p1004Cp4p710R5p8P0p1004ap4p7210R6p8P0g005>R0p4p710R7p8g028`R8p4p710R9P4p8P9P7p8p10069p4p70R:p1006gp4p7210p8P:P4p8P:p101M\p4p710p8P:P9p8P:P5p8P:P6p8P:p101NRp4p710p8P:p101ONp4p710p8P:P7p8P:g007CR:p4p710p8p1007`p4p7210R9P1p8P9P2p8P9P4p8P9P5p8P9P6p8P9p1008Lp4p7210p8P9P7p8P9P3p8P9p100`0p4p710p8p1008ip4p70R9P4p8P9P5p8P9P6p8P9P7p8p1009_p4p710R9P4p8P9P7p8g00<lj1;Tg00=Qj1ZTg00OJj1QTg00Jcj1JTg01U_j1YTg00oFj1WTg00?\j30Tg00PMj2PTg00Omj1ATg01PHj1KTg00Pmj1CTg00e8j1HTg01Q@j2=Tg01jEj4?Tg01[gj11Tg01kVj1Vj3XTg029@j5UTg02:Aj7TTg02;;j4RTg02<9j47Tg00VBR7j22Tg00UhR9j2>Tg00>Yj18Tg00?>j1OTg00Ndj2MTg00RKj3LTg01\Zj2<Tg00HgR4j25Tg021Aj3BTP8j5ITg00V]j2DTg00mTj3GTP0j8ETg00mnj3STP:j3FTg01_cj3@Tf3R:g00[<R0f2R8f1R63Ff0R53Xp=4A@06590:8p=3%15,<6p=6AF065p=:A@065p=N1<86=@05p=9g00c7g00G3g00I_R3#;#;#;#;#;#;#ZR2#QR1#J%Y5%W1301P11R1#A%K6%C130%H:%A0R1g01`Cp,4segsR;f6R<f5R='=P6P5C?P;P6g027fR>f8R?#1R@f4RAP6P5C4W0X61P;f7RB/=<%1<#VP8P6PBP<P=PAP:DUP5FTCRP;P:P6P5C7f:RC#1P<P6P5C4X0>X61P6P5O2'2X0>,>>X41,>1P9P1P;PAP6P5C7f9RD#1P=P6P5C4'2X0>,>>X41%C0RE901AP1PAp,4code%83#8#8#8#8#8#8#O,M25L2R2/<@PEC3'5P5P;P<P6P5C7f;R<#1PBP6P5C4'2X0>,>>P9P>P;PBP8P5C7f<R9#1R@P?P8P5C4'2X0>A01?EP1P?1<2@PEC3'5P5P;PDPAP5C7f>R@#1PCPAP5C4'2P7P;PCP=P6C7f?RC#1P<P=P6C4A019EP1P9f@R8,62PEC3'5P5P;P9PBP:C7fBR3#1P@P?PAC4P7P11:CDRDfCRA,62PEC3AB2D=A018ERDP1P8fDR=,62PEC3'5P5P1fA/:<fER<,62PEC31:39=B2?P0PAf=R0fGR?,62R3P6DIA01AE1N3ER39010'2A01A3A010E'2'5P4A01=EfHR4#1=92ER0901@'2A01=0A01@E'2A01<ER@fIR0#1=92ER3901<RA'5P5A01C3,2@P7fFR3=01ER9fJ#1=92ERF9018A01?EP1P?fK,62PEC3'5R8P5A014EP1PEP;fORGfNRH'=P5P0C?RI1:6<%1G=92ERG501RJfP#1=92ERK9013A01:EP1P:fQ,62PEC3'5R:[]2]3X41P;fMRL,=HRMPEP4C?1:E=%1H=92ERH501A01<GA01EEA01EK1D1E3GW5W2W3P0P5P?PBGEW1P6P5O2n2001000000121000000W1P5O1A01CE,2AP7A013FPDP8P5P1P4fL,62PEC3P1%1L=92ER2P:\9^2J^3IX41P;PMP2P4C?1:H==01HA01KEA01KK1D1K3SX5@W2W3P0P5P?PBGEW1P6P5O2n2001000000121000000W1P5O1n200100000021100011000b?W5W2P6P5O2n2001000000121000000W7W5P6P5O2n2001000000121000000W1X0>P6P5O2n2001000000121100000W1X61P6P5O2n2001000000121100000b<W3W;W4W:W9W8W=W>o"). Qed.

Lemma to_exit_star_admits : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  exists c, star segs (mkCfg ms model)
              [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)] c.
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) ["WithSegs"] "p'0h01ci001ch11Hh22Hmh32Hxh41oi011oh52trh63Heqh72c'h82Hhh95Hlazyh:5Hstarh;3Hteh<2_Hh=1ah>1eh?5modelh@2mshA1xi021xp;1p;3p;2p;5p;4p;7p;8p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0p1003gp4p710R4p8P0p1004Cp4p710R5p8P0p1004ap4p7210R6p8P0g005>R0p4p710R7p8p1005\p4p710R8P4p8P8P7p8p10069p4p70R9p1006gp4p7210p8P9P4p8P9p101M\p4p710p8P9P8p8P9P5p8P9P6p8P9p101NRp4p710p8P9p101ONp4p710p8P9P7p8P9p1007Cp4p710p8p1007`p4p7210R9P1p8P9P2p8P9P4p8P9P5p8P9P6p8P9p1008Lp4p7210p8P9P7p8P9P3p8P9p100`0p4p710p8p1008ip4p70R9P4p8P9P5p8P9P6p8P9P7p8p1009_p4p710R9P4p8P9P7p8g00<lj1=Tg00=Qj1WTg00OJj1PTg00Jcj1ITg01U_j1?Tg00oFj1TTg00?\j39Tg00PMj2OTg00Omj1DTg01PHj1JTg00Pmj1ETg00e8j1GTg01Q@j20Tg01[gj15Tg01kVj1Vj34Tg029@j5UTg02;;j4STg02<9j41Tg00VBR7j27Tg00UhR9j2>Tg00>Yj1:Tg00?>j1NTg00Ndj2MTg00RKj3KTg01jEj42Tg020Gj16Tg021Aj3;Tg00V]j2HTg02=1j7LTg01iOj1@Tg00^Bj1ATg00WRj4QTP0j8RTg02>1j1<Tg01\Zj2BTg01_cj3FTg00[<R0f2R4f1R6'Bf0R53Fp=Cg01`CR3/>5p=8%56,B4=F05p=3g00c7g00G3g00I_R2#=#=#=#=#=#=#WR1#PR8#IR:%?5%T8R;391O88R8#D%J6%E839f3R8#Gp,4segsR<f4R=/08%58#VP=P8P4P6P5DUCS%D0R>g027fR?P<f6R@f5RA'0P6P5C1%5A?465'7X4?'>X5>'>P9P>P<f7RB/0@RCP6P5C1%5@RD?465'7X4?,>?X5>P<PCp,4code%:2#:#:#:#:#:#:#N,M15K1R1%E0R07CDP5C2X03#8P5P<f9RDf8R2'0P6P5C1%52?465'7X4?,>?P9P?P<f:R9/0DP4P5C1%5D?445'7X4?P<f;R4/09A3190P5C2X03#8P5P?P<f=RCf<RE'0PAP5C1%5E?4A5'7P<f?RFf>RG'0RH%5GRI=C10P5C2X03#8[P5P<10GCRJP@%65RKC1%5CRL?4@K'7P7P<PHPB%66RKC1A4IBKP<fARKf@RM'0RNA31M0P5C2X03#8ROP5P<PNPD%68C1%5KRK%6=749P7fB=31099>4RP%6A9;14P<fEfDRQ'0A31Q0RQP5C2X03#8RRP5A9>CQRQ%629;1GP>fFRC=310RSP<fHRTfGRU'0P5%69RVC1%64RW9;16P<fKRXfJRY'0A31Y0P5C2X03#8]3]2X5>P<10UCPS%6DC1A31U0=;1VP<fIRV/0TRUA31T0RTPWP6P41H?WFLP<PUPTP4C2%@4#?=9:;#A'7P7P<10YVA31V0PEC2%@E#?=9:;#AP<fL/0XREA31X0RXP5C2X03#8P5P<PEPXPGC2%@F#?=9:;#AP3P<fOfNR;'0A31;0P5C2X03PMP6CQW<W:P6P5O2n2001000000120000000b=W3W2PFP6PAP5GRW3W6P6P5O2n2001000000121000000W1W2P6P5O2n2001000000121000000W1X73P5O1P<PJP@%<5RJC1A4L@J'7P7P<PHPB%<6RHC1A4IBHPOP5P<PNPD%<8C1%<=94K9P7PP%<A9;14PRP5%<29;1Gg00^[P<PUPTP5C2X03#8P5n010000000W3X6QP6P5O2n2001000000120000000W1W2P6P5O2n2001000000121000000W1X73P5O1n0110100021110011100XA?P6P5O2n2001000000121102000W1X5>P6P5O2n2001000000121102000b>W;W9W8W?W@o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition on_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   to_exit (cfg_ms c))
  \/ m_halted (cfg_model c) <> None.

Lemma on_path_step : forall c evs c',
  on_path c -> sstep segs c evs (SNext c') -> on_path c'.
Proof.
  (* Ported by name from 727298f3:theories/Common/ExitSim.v, [on_path_step].
     The recorded KReplay term this replaces case-analyses [sstep], whose arm
     count went 8 -> 11 at 727298f3 (the three [sstep_vdso_*] arms), and the
     replay engine builds its [Case] with the RECORDED branch count against
     the inductive AS IT IS NOW.  The kernel then raised
     `Anomaly "decompose_lambda_n_decls: not enough declarations."` at the
     Qed (a build round, image
     sha256:32a9f8ef).  Statement unchanged. *)
  intros [ms model] evs [ms' model'] Hop Hss.
  unfold on_path in *; cbn in Hop |- *.
  destruct Hop as [[Hh [Hlazy Hte]] | Hh].
  - destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
    + (* te_here *)
      destruct (sstep_exit_inv ms0 model x8 evs (SNext (mkCfg ms' model'))
                  Hh Hsvc Hx8 Hss) as [_ Hc'].
      inversion Hc'; subst. right. cbn. discriminate.
    + (* te_step *)
      destruct (sstep_instr_inv ms0 model ms0' evs (SNext (mkCfg ms' model'))
                  Hlazy Hsvc Hstep Hss) as [_ Hc'].
      inversion Hc'; subst. left. repeat split; assumption.
  - (* already halted: no sstep possible *)
    exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.

Lemma on_path_no_error : forall c evs, on_path c -> ~ sstep segs c evs SError.
Proof.
  (* Ported by name from 727298f3:theories/Common/ExitSim.v, [on_path_no_error];
     same recorded-[sstep]-case cause as [on_path_step] above. *)
  intros [ms model] evs Hop Hss.
  unfold on_path in *; cbn in Hop.
  destruct Hop as [[Hh [Hlazy Hte]] | Hh].
  - destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
    + destruct (sstep_exit_inv ms0 model x8 evs SError Hh Hsvc Hx8 Hss) as [_ Hc'].
      discriminate.
    + destruct (sstep_instr_inv ms0 model ms0' evs SError Hlazy Hsvc Hstep Hss) as [_ Hc'].
      discriminate.
  - inversion Hss; subst; cbn in Hh; congruence.
Qed.

Lemma star_on_path : forall c tr c',
  on_path c -> star segs c tr c' -> on_path c'.
Proof.
  (* 727298f3:theories/Common/ExitSim.v, [star_on_path]. *)
  exact (star_inv segs on_path on_path_step).
Qed.

Lemma to_exit_no_error : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  (* 727298f3:theories/Common/ExitSim.v, [to_exit_no_error]. *)
  intros ms model Hh Hlazy Hte. apply exec_no_error.
  eapply exec_conseq; [exact (to_exit_exec ms model Hh Hlazy Hte) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegs.

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

Definition overlay_argc_bytes (sp : word) (argc : nat)
    (base_mem : word -> option byte) : word -> option byte :=
  let bytes := word_le8 (nat_to_word argc) in
  fun addr =>
    if (bv_unsigned addr =? bv_unsigned sp)%Z then nth_error bytes 0
    else if (bv_unsigned addr =? bv_unsigned sp + 1)%Z then nth_error bytes 1
    else if (bv_unsigned addr =? bv_unsigned sp + 2)%Z then nth_error bytes 2
    else if (bv_unsigned addr =? bv_unsigned sp + 3)%Z then nth_error bytes 3
    else if (bv_unsigned addr =? bv_unsigned sp + 4)%Z then nth_error bytes 4
    else if (bv_unsigned addr =? bv_unsigned sp + 5)%Z then nth_error bytes 5
    else if (bv_unsigned addr =? bv_unsigned sp + 6)%Z then nth_error bytes 6
    else if (bv_unsigned addr =? bv_unsigned sp + 7)%Z then nth_error bytes 7
    else base_mem addr.

Lemma stm_at (sp : word) (bytes : list byte) (addr : word) (i : nat) :
  (i < length bytes)%nat ->
  bv_unsigned addr = (bv_unsigned sp + Z.of_nat i)%Z ->
  stack_to_mem sp bytes addr = nth_error bytes i.
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) [] "p'0h04__x1h14__x2h22E1h32E2h44__p1h51xh61yh71Hh83Hi0h97__arithh:4__ffh;8__varmaph<5__with=4cstrh>5cstr0h?4addrh@1bi001bhA5byteshB1ihC2sphD1zhE5HaddrhF2HihG1np;1p;2p;3p;4p;6p;<p;7p;8p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0g002WR0p4p710p8p10037p4p70R4g003gR5p4p710R6p8P4p1004Cp4p710R7p8P4p1004ap4p7210R8p8P4g005>R4p4p710R9p8p1005\p4p710R:P6p8P:P9p8p10069p4p70R;p1006gp4p7210p8P;P6p8P;p101M\p4p710p8P;P:p8P;P7p8P;P8p8P;p101NRp4p710p8P;p101ONp4p710p8P;P9p8P;p1007Cp4p710p8p1007`p4p7210R;P1p8P;P2p8P;P6p8P;P7p8P;P8p8P;p1008Lp4p7210p8P;P9p8P;P3p8P;p100`0p4p710p8p1008ip4p70R;P6p8P;P7p8P;P8p8P;P9p8p1009_p4p710R;P6p8P;P9p8g00<lj1:Tg00=Qj1OTg00OJj1MTg00Omj1KTP0j23Tg02F?R0j2ETg00=oj24Tg02FWR9j10Tg02G7j26Tg00?\j31Tg00Jcj1WTg02GTj29Tg02H1j2BTg02HNj25Tg02Hkj1>Tg02IKj32Tg00oFj1PTg00V]j2FTg02IiR;j27Tg02JEj4HTg02Jlj1;Tg00Pmj1[Tg02KQj2NTg02Koj1ZTg02LMj4CTg02Lkj1YTg02MIj1XTg02N4j2DTg02NWj3LTg02O:j3VTg02O]j4@Tg02PHj2UTg02Pjj2RTg02QVj3STg02R5j4TTg02Rgj1fTP4j6QTg02SEj2=Tg02Saj2eTg00>Yj1dTg02TAj6cTP5j6bTg02Tej2^Tg02UEj2]Tg02Uhj3_Tg02Vil<\Tg02WNj7`Tg02X2j8aTg015gR5f0R4g016GR631p=Jg00IAR8/F4p=<g00Z]R7P8P0P9P;g02XVf5R;f4R9f3R0f2R3f1R2P4M<\p=Ig00YGR1/=4p=8P2g02Y8R:g00XGR<P<g02YWR=P4g00XgF`p=Ag016g9154p=?P0P:P<P<P=P3P2P4Gap=Gg00I_R>#:R?#:R@#:RA#:#:#:#ORB#MRC%OA#MRA#KRD13A3,E414B314B9%02'6518P814B;RE%03'6RF%WARGP5PGf6RH,4BRI/94P5PG1B4IRJ13A;#0'5%>J92A;%PARJn0100000020000PJn0100000020000A2A;031XD819EFRKP51F54RL%00,6I,9I=154P5f8RI,4BRM%0;RN,6MRO'9=154P5PGP2P5PGf9RP,4BRQ%0HRR'6RS/BQRT13AI#0RU'5%>T92AIPJn0100000020000PJn0100000020000A2AIH51G]2P2f7RV,4BRW%09,6W'9RW#J13AVRX,E;%0XRY,7NRZP;PN%<NPXPY%<YEIP9CHPZ%;H%8R13APRZ#;%0ZRY#8g02Z7RX#[R[%KXRXP81N83R\P2%Z8R]CC%Y8R^%X8R_P81D8>R`g02Zc1D8?R?=L8`=V8?C@'A1U_=R`P4P31F561R43#JdAS812CTR6b:b;b<X08X181624/B29184^08^18P4f<Ra,4B%0PRbO2b9b>b=b81BOM918NP8PRP5PG154Y%>492APPJn0100000020000A2APV51GXD815RUP5PL%0VRL/5Y=154P5f;RU,3ARR#0RN,5b=154P5PGP2f:RO#0RM#>92AaPJn0100000020000A2AaORc51G]3P2%0IRd13AO#0'5Re#JP7PPA2Aa4=1GcXG7A2AUP,FG%>b%fPEQW3%?eg00VBRe1524#?1=23[RP1=421532#?Rb[1=30\b1e24P2n2001000000120000000X68X58PP^68^58P4PM13Aa#0RPP2O31=PMf=RP,3ARM,EU%0URb%0MRc'7RfPUPb%<bPMPc%<cEIPOCHPf%;a%0a#8f?Ra,3ARf#;%0f#8p-0RfP[PXP8P8P\P3P]CCP31N82R]CCP^P_P8%d>,D8R>g02[JRO1D8@R@C@,A_%P<RcP_P8P@g02\1R@P>C@,A_PcP_P:P<P<P=P9EcR=CGCGP`P6b:b;b<X08X18W41742R<1=32P9[[^08^18^4fP4fAR:=2Aa91GJ13A:#0%0aP0P9O5b9b>b=b8b3b7W3n0110000020001P4O1b3b@PTP4Ebb7W2%?WPe1924#?1723[Re1932#?RW\<1730\W1^24P2n2001000000120000000X68X58Pe^68^58P4PQPSP2O317SQ1EVZ17LYRSPVPL%<LPZPY%<YEIPHCHPS%;I%8d%;R%8NP[PXP8P]P3P\CCP^P_P81]81P@P>C@,A_PcP_P8AL8?>POP?C@,A_PcP=CGCGP`P6b:b;b<X08X18X4f%821623/72P9[[^08^18^4fP4A2APU91GJPbf>,4BP3P9O5b9b>b=b8b2b7W2n0110000020101P4O1b2b@P5PGPKP5PG1BFERF13A9#0'5%>F92A9PJn0100000020000PJn0100000020000A2A93RA51Ge14B0P4EQA_;90=1GAeWEWFXB7X?CXADXCCP0P3P2P4O4XB7X?CWAWCo"). Qed.

Lemma build_stack_starts_with_argc :
  forall inp mbase ph entry (sp : word) draw,
  exists rest,
    entry_stack_image inp mbase ph entry sp draw =
    word_le8 (nat_to_word (length (in_argv inp))) ++ rest.
Proof.
  intros inp mbase ph entry sp draw.
  unfold entry_stack_image, build_stack_bytes, len_word, nat_to_word.
  cbv zeta.
  destruct (string_addrs _ (in_argv inp)) as [? ?].
  destruct (string_addrs _ (in_envp inp)) as [? ?].
  eexists. exact (eq_sym (app_assoc _ _ _)).
Qed.

Lemma word_le8_length : forall v, length (word_le8 v) = 8%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) [] "h01vp;1p;2p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0p1003gp4p710R4p8P0p1004Cp4p710R5p8P0p1004ap4p7210R6p8P0p1005>p4p710R0p8p1005\p4p710R7P4p8P7P0p8p10069p4p70R8p1006gp4p7210p8P8P4p8P8p101M\p4p710p8P8P7p8P8P5p8P8P6p8P8p101NRp4p710p8P8p101ONp4p710p8P8P0p8P8p1007Cp4p710p8p1007`p4p7210R8P1p8P8P2p8P8P4p8P8P5p8P8P6p8P8p1008Lp4p7210p8P8P0p8P8P3p8P8p100`0p4p710p8p1008ip4p70R8P4p8P8P5p8P8P6p8P8P0p8p1009_p4p710R8P4p8P8P0p8g00<lj11Tg00=Qj14Tg00OJj12Tg00f6j10Tg00V]j23Tg00I_#1#1#1#1#1#1#4#2g00Z]g00JD#0#0#0#0#0#0#0#0'3W0o"). Qed.

Lemma build_stack_min_length : forall inp mbase ph entry (sp : word) draw,
  (8 <= length (entry_stack_image inp mbase ph entry sp draw))%nat.
Proof.
  intros inp mbase ph entry sp draw.
  destruct (build_stack_starts_with_argc inp mbase ph entry sp draw)
    as [rest Hr].
  rewrite Hr, length_app, word_le8_length. lia.
Qed.

(* [comment removed for export] *)
Lemma init_first8 :
  forall segs init_pc ph init_sp mbase init_rnd inp addr i, (i < 8)%nat ->
  bv_unsigned addr = (bv_unsigned init_sp + Z.of_nat i)%Z ->
  ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp) addr =
  nth_error (word_le8 (nat_to_word (length (in_argv inp)))) i.
Proof.
  intros segs init_pc ph init_sp mbase init_rnd inp addr i Hi Haddr.
  assert (Hstk : stack_to_mem init_sp
                   (entry_stack_image inp mbase ph
                      (Z_to_bv 64 (Z.of_N init_pc)) init_sp init_rnd) addr
                 = nth_error (word_le8 (nat_to_word (length (in_argv inp)))) i).
  { rewrite (stm_at init_sp _ addr i);
      [ | pose proof (build_stack_min_length inp mbase ph
                        (Z_to_bv 64 (Z.of_N init_pc)) init_sp init_rnd); lia
        | exact Haddr ].
    destruct (build_stack_starts_with_argc inp mbase ph
                (Z_to_bv 64 (Z.of_N init_pc)) init_sp init_rnd) as [rest Hr].
    rewrite Hr. apply nth_error_app1. rewrite word_le8_length. lia. }
  change (ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp)
            addr)
    with (match stack_to_mem init_sp
                  (entry_stack_image inp mbase ph
                     (Z_to_bv 64 (Z.of_N init_pc)) init_sp init_rnd) addr with
          | Some b => Some b
          | None =>
              if andb (Z.leb (stack_window_lo (in_kernel inp) mbase init_rnd)
                             (bv_unsigned addr))
                      (Z.ltb (bv_unsigned addr) (bv_unsigned init_sp))
              then Some (Z_to_bv 8 0) else None
          end).
  rewrite Hstk.
  destruct (nth_error (word_le8 (nat_to_word (length (in_argv inp)))) i) eqn:E;
    [reflexivity|].
  apply nth_error_None in E. rewrite word_le8_length in E. lia.
Qed.

Lemma actual_mem_is_overlay :
  forall segs init_pc ph init_sp mbase init_rnd inp,
  ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp) =
  overlay_argc_bytes init_sp (length (in_argv inp))
    (ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp)).
Proof.
  intros segs init_pc ph init_sp mbase init_rnd inp.
  apply functional_extensionality. intro addr.
  unfold overlay_argc_bytes.
  destruct ((bv_unsigned addr =? bv_unsigned init_sp)%Z) eqn:E0;
    [ apply Z.eqb_eq in E0;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 0); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 1)%Z) eqn:E1;
    [ apply Z.eqb_eq in E1;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 1); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 2)%Z) eqn:E2;
    [ apply Z.eqb_eq in E2;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 2); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 3)%Z) eqn:E3;
    [ apply Z.eqb_eq in E3;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 3); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 4)%Z) eqn:E4;
    [ apply Z.eqb_eq in E4;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 4); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 5)%Z) eqn:E5;
    [ apply Z.eqb_eq in E5;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 5); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 6)%Z) eqn:E6;
    [ apply Z.eqb_eq in E6;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 6); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 7)%Z) eqn:E7;
    [ apply Z.eqb_eq in E7;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 7); lia | ].
  reflexivity.
Qed.

Lemma machine_state_eta : forall ms : machine_state,
  ms = {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
          ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
          ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.
Proof.
ltac2:(KReplay.run1 (kr_t_ExitSim ()) [] "p'0h02msh17ms_fcsri007ms_fcsrh28ms_fregsi018ms_fregsh36ms_memi026ms_memh49ms_pc_vali039ms_pc_valh57ms_regsi047ms_regsh67ms_resvi057ms_resvh76ms_romi066ms_romh8>ms_svc_pendingi07>ms_svc_pendingi081mp;1p;8p;3p;2p-1R0p10000p4p710R1p9P0p100N8p4p710R2p9P0p1001AR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001_p4p710R3p9P0p1002Wp4p710p8p10037p4p70R0p1003gp4p710R4p8P0p1004Cp4p710R5p8P0p1004ap4p7210R6p8P0p1005>p4p710R0p8p1005\p4p710R7P4p8P7P0p8p10069p4p70R8p1006gp4p7210p8P8P4p8P8p101M\p4p710p8P8P7p8P8P5p8P8P6p8P8p101NRp4p710p8P8p101ONp4p710p8P8P0p8P8p1007Cp4p710p8g007`R8p4p7210R7P1p8P7P2p8P7P4p8P7P5p8P7P6p8P7p1008Lp4p7210p8P7P0p8P7P3p8P7p100`0p4p710p8p1008ip4p70R7P4p8P7P5p8P7P6p8P7P0p8p1009_p4p710R7P4p8P7P0p8g01:gj1:Tg01;fj1<Tg01<fj17Tg00fUj14Tg01=gj1;Tg01>fj18Tg01?ej19Tg01@cj16Tg01Aaj82Tg00?\j3>Tg00<lj10Tg00>Yj1=Tg00=Qj11Tg00OJj13TP8j2@Tg00Jcj15Tg00V]j2?Tg00c7R8P8f0R0%:0%<0%70%40%;0%80%90%60G25>8P0g00I_#0R7#=#1%07#0R7#0#0R4#0#1#3R6'@R5%56R3%14#3%17#3#5\6R7f7R4f6R2f5R1f4R9f3R:f2R;f1R<P0G2R=#:%<=%7=%4=%;=%8=%9=%6=G2,?8X77W3W1X63W8X46X25W5P4P2P1P9P:P;P<P0O8n01108000181104101103107105100102106W0o"). Qed.

(* [comment removed for export] *)
Definition enum_state (segs : list Segment) (init_pc : N) (ph : PhdrInfo)
    (init_sp mbase : word) (init_rnd : EntryDraw) (inp : ProcInput)
    (argc : nat) (base : word -> option byte) : machine_state :=
  {| ms_regs       := ms_regs (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_fregs      := ms_fregs (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_pc_val     := ms_pc_val (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_svc_pending := ms_svc_pending (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_resv       := ms_resv (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_fcsr       := ms_fcsr (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_mem        := overlay_argc_bytes init_sp argc base;
     ms_rom        := ms_rom (init_machine_state segs init_pc ph init_sp mbase init_rnd inp) |}.

(* [comment removed for export] *)
Lemma init_eq_enum_state :
  forall segs init_pc ph init_sp mbase init_rnd inp,
  init_machine_state segs init_pc ph init_sp mbase init_rnd inp =
  enum_state segs init_pc ph init_sp mbase init_rnd inp
    (length (in_argv inp))
    (ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp)).
Proof.
  intros segs init_pc ph init_sp mbase init_rnd inp. unfold enum_state.
  rewrite (machine_state_eta
             (init_machine_state segs init_pc ph init_sp mbase init_rnd inp)) at 1.
  f_equal; try reflexivity. apply actual_mem_is_overlay.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exit_omni_run : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (exit_post code (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim.
  cbn [omni_run]. unfold init_config.
  exact (to_exit_exec (run_segments segs inp sp mb) code
           (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           eq_refl eq_refl (sim_c_to_exit (run_segments segs inp sp mb) code F _ Hsim)).
Qed.

Lemma exit_obs_iff : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  forall tr, obs_trace (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr [ExitEv (bv_and code (Z_to_bv 64 255)) (in_fs inp)].
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim tr.
  apply exec_obs_iff.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

Lemma exit_no_error_run : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  ~ reaches_error (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply exec_no_error.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma exit_must_exit_with : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  must_exit_with (bv_and code (Z_to_bv 64 255)) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply must_exit_with_iff.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr o (_ & Hx). exact Hx.
Qed.

Lemma exit_omni_run_code_unique : forall segs pc ph sp brk0 mb rnd lim code inp F code',
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') ->
  code' = bv_and code (Z_to_bv 64 255).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F code' Hsim Hex.
  pose proof (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) as Hrun.
  cbn [omni_run] in Hrun, Hex.
  destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.

(* [comment removed for export] *)
Lemma exit_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA,
  sim_c (run_segments source_segs inp rsp rmb) code FR
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) = true ->
  sim_c (run_segments target_segs inp asp amb) code FA
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA
    Hsource Htarget.
  split.
  { cbn [image_run_segments img_segments en_sp en_mmap_base].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (exit_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource) |].
    intros tr o (_ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource tr).
    rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (exit_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget).
Qed.

(* [comment removed for export] *)
Lemma exit_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA,
  sim_c (run_segments source_segs inp rsp rmb) code FR
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) = true ->
  sim_c (run_segments target_segs inp asp amb) code FA
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA
    Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    apply (exit_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource tr).
    rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd alim code inp FA Htarget tr).
    reflexivity.
  - cbn. apply (exit_no_error_run target_segs apc aph asp abrk amb arnd alim code inp FA Htarget).
Qed.

End ExitSim.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Fs.ReadWrite.
Module CatSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_CatSim () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp7tactics<f_equal_helpC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<ms_read_byteC4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_auxC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsAms_read_bytes_auxI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addK47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesc59OSSVerify5KrLib7Mh_00306CatSimBread_aux_read_byteC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_mapC4ELinuxProcessSemantics?LinuxProcessSem5StateAread_bytes_map_eqK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7set_regI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC47Corelib7Classes?RelationClasses;reflexivityI4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome00C45stdpp9bitvector;definitions;bv_unsignedC5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch:lookup_armC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7sa_specC4ELinuxProcessSemantics?LinuxProcessSem5Monad9unmodeledC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite:write_specC47Corelib4Init5Logic3iffC4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I47Corelib7Numbers7BinNums1Z00I5ELinuxProcessSemantics?LinuxProcessSem3Sys8Dispatch7SpecArm00C5ELinuxProcessSemantics?LinuxProcessSem3Sys<SyscallTable:spec_tableC47Corelib7Classes?RelationClasses=iff_Reflexivec59OSSVerify5KrLib7Mh_00306CatSim;buf_modeledC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkappK47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxC46Stdlib5Lists4List<length_skipnC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06C47Corelib5Lists7ListDef5skipnC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib5Lists4List=length_firstnc59OSSVerify5KrLib7Mh_00306CatSim7fd1chanC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Peano2le00c59OSSVerify5KrLib7Mh_00306CatSimHread_bytes_map_read_byteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00306CatSim@in_mem_sys_inputC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeEread_bytes_map_lengthC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeCword_unsigned_rangeK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ELinuxProcessSemantics?LinuxProcessSem3Sys7UaccessArw_range_in_rangeC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@modeled_rw_rangeC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7UaccessDcheck_access_ok_zeroC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6to_natC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAaccess_ranges_eqbK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C47Corelib4Init9Datatypes4andbC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite@modeled_file_gapK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry03C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC4ELinuxProcessSemantics?LinuxProcessSem2Fs:file_writeC4ELinuxProcessSemantics?LinuxProcessSem2Fs6fs_setC4ELinuxProcessSemantics?LinuxProcessSem5State7with_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeFcheck_ret_only_copyinsC4ELinuxProcessSemantics?LinuxProcessSem5State:access_okbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite>rw_pos_einvalbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite>append_new_posK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry04K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry05C4ELinuxProcessSemantics?LinuxProcessSem5State=pipe_end_liveC4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC4ELinuxProcessSemantics?LinuxProcessSem5State;pipe_lookupC4ELinuxProcessSemantics?LinuxProcessSem5State?pipe_write_roomC56Stdlib5Arith8PeanoNat3Nat3eqbC4ELinuxProcessSemantics?LinuxProcessSem5State;pipe_appendC4ELinuxProcessSemantics?LinuxProcessSem5State;pipe_insertC4ELinuxProcessSemantics?LinuxProcessSem5State:with_pipesC4ELinuxProcessSemantics?LinuxProcessSem5State>rw_count_clampK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<write_sourceC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall9w_is0_posC4ELinuxProcessSemantics?LinuxProcessSem5State>readable_bytesC47Corelib4Init5Logic3notC56Stdlib5Arith8PeanoNat3Nat7eqb_neqC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphK46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAlen_word_unsignedC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib5Arith8PeanoNat3Nat8eqb_reflC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude;bv_eqb_reflC56Stdlib6ZArith4Znat5Nat2Z2idC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeCreadable_bytes_fullC5ELinuxProcessSemantics?LinuxProcessSem3Sys7UaccessBwrite_source_of_rwC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWrite;check_writeC4ELinuxProcessSemantics?LinuxProcessSem5State6in_memC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init9Datatypes4prod01K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00K46Stdlib9micromega=RingMicromega3Op205C56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State5EBADFK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03C4ELinuxProcessSemantics?LinuxProcessSem5State6EFAULTK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALI47Corelib4Init5Logic5False00K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01c59OSSVerify5KrLib7Mh_00306CatSimBsyscall_spec_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00306CatSim>write1_check_nC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWriteDcheck_write_sound_okC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWriteGcheck_write_complete_okC47Corelib4Init5Logic9False_indC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeCwrite_source_prefixC4ELinuxProcessSemantics?LinuxProcessSem5StateDrw_count_clamp_rangeC57Corelib7BinNums6PosDef3Pos6to_natC46Stdlib4Bool4Bool=andb_true_iffC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeDaccess_ranges_eqb_eqC46Stdlib5Lists4List=firstn_firstnC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeClen_word_firstn_retK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI47Corelib4Init5Logic4True00C4ELinuxProcessSemantics?LinuxProcessSem5State<MAX_RW_COUNTK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWriteNcheck_write_complete_unmodeledC47Corelib4Init5Logic6eq_symC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeKcheck_ret_only_no_unmodeledC47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00306CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_allI47Corelib5Lists7ListDef6Forall00c59OSSVerify5KrLib7Mh_00306CatSim:wevents_chC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00306CatSim5wpick00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00306CatSim5wpick01C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7le_reflk59OSSVerify5KrLib7Mh_00306CatSim5wpick02C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef:Forall_indI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01k59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00306CatSim:msteps_indC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00306CatSim8to_wexit00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00306CatSim8to_wexit03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00307ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcc59OSSVerify5KrLib7Mh_00306CatSim<to_wexit_indC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepI4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03c59OSSVerify5KrLib7Mh_00306CatSim=write1_ok_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyc59OSSVerify5KrLib7Mh_00306CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5StateIm_killed_of_m_halted_noneK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02c59OSSVerify5KrLib7Mh_00306CatSimDsstep_write_next_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00306CatSimCwrite1_no_unmodeledC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rc59OSSVerify5KrLib7Mh_00306CatSim<bufs_modeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00306CatSim:wexit_postC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec00C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoc59OSSVerify5KrLib7Mh_00307ExitSimBin_sysno_sys_inputC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00307ExitSim@exit_dispatch_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_killed_with_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep06c59OSSVerify5KrLib7Mh_00307ExitSim>sstep_exit_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_halted_with_haltedC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exits_withK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun>exec_step_onlyC46Stdlib5Lists4List?Forall_cons_iffc59OSSVerify5KrLib7Mh_00306CatSim;write1_ok_nC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04c59OSSVerify5KrLib7Mh_00306CatSim?sstep_write_invC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome02C46Stdlib5Lists4List9app_assocC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_conseqK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec02C4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01c59OSSVerify5KrLib7Mh_00307ExitSim?sstep_instr_invC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome00I46Stdlib5Lists4List6Exists00I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00C4ELinuxProcessSemantics?LinuxProcessSem3Run8star_oneK4ELinuxProcessSemantics?LinuxProcessSem3Run4star02c59OSSVerify5KrLib7Mh_00306CatSim=to_wexit_execC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun9exec_starC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_realizesI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun5mexec00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunGexits_with_never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_no_errorI4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun8omni_runI47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C4ELinuxProcessSemantics?LinuxProcessSem3Run9obs_tracec59OSSVerify5KrLib7Mh_00306CatSimBto_wexit_star_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00306CatSimDto_wexit_star_admitsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00306CatSim?cat_omni_run_teC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit>must_exit_withC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalenceBmust_exit_with_iffI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exec_soundC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<img_segmentsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:omni_corunC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence:omni_equivC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_coexecC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunDnever_errors_coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=coexec_conseqC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence@omni_trace_equivC4ELinuxProcessSemantics?LinuxProcessSem3Run3runC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalenceDtrace_equiv_iff_omnic59OSSVerify5KrLib7Mh_00306CatSim>cat_obs_iff_teC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=bh_errors_iffc59OSSVerify5KrLib7Mh_00306CatSimCcat_no_error_run_teC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6errorsC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence7modeledC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence5equivC59OSSVerify5KrLib7Mh_00266SimInvDno_error_run_modeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=bh_all_errorsc59OSSVerify5KrLib7Mh_00306CatSim6fdchanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00306CatSim@write_ch_check_nC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00306CatSim;to_wexit_ch00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00306CatSim;to_wexit_ch03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00306CatSim?write_ch_ok_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00306CatSimEwrite_ch_no_unmodeledC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00306CatSim;to_wexit_ch01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00306CatSim;to_wexit_ch02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00306CatSim7weventsC1?~~~~~~~~~~~~~~~".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read_aux_read_byte : forall ms k a,
  read_bytes_aux (ms_read_byte ms) a k = ms_read_bytes_aux ms a k.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "p'0h01ah11kh21oi001oh32IHh41bi011bh52msi021ri034resti041xp;1p;3p;2p;6p;4p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0g005<R0p4p710R7p8p1005Zp4p710R8P4p8P8P7p8p10067p4p70R9p1006ep4p7210p8P9P4p8P9p1007Ap4p710p8P9P8p8P9P5p8P9P6p8P9p10087p4p710p8P9p10093p4p710p8P9P7p8P9p1009mp4p710p8p100:Jp4p7210R9P1p8P9P2p8P9P4p8P9P5p8P9P6p8P9p100;6p4p7210p8P9P7p8P9P3p8P9p100;Sp4p710p8p100<]p4p70R9P4p8P9P5p8P9P6p8P9P7p8p100=Sp4p710R9P4p8P9P7p8g00>2j10Tg00>Wj18Tg00?5j17Tg00?Xj1?Tg00@8R7j1;Tg00@Zj13j2>Tg00A^j35Tg00B[j31Tg00Cdj32Tg00D>j24Tg00DXj1=Tg00E6j3<Tg00EYj3:Tg00F>j39Tg00F^j26Tg00G@j1CTP0j6BTg00Gbj1ATg00HAj4@Tg00Hbg00IiR0g00JHR9#0#0#0R4#0#0#0#8R6#7R5%84#7R4#?R3#;R2f3R1#3f0R8f1R:35A118:32]0R;X10f2R<g00Jm718,42X05f4R=/>8%;4P7P4P7P4P2P8P7P3P2f7R>#3%=9g00KL5<6R99:61R1f5R?35R@A94:8,63R:%C3RAn10110400021010200PAn10110400021010100P7P4P2P8P7P3P2A1>1?R?P:PAn10110400021010300R:PAn10110400021010100522P8P2P?P7P3P2P8A94<8,63R?PAn10110400021010200P7P3P2f8A:6=9f631P?PAn10110400021010300522X22142:P@P=P1O1EBX44P8O1142An10110001021110100b2%3=%A<R<758A1=8<522eX05X3;X10P8C@W1W5o"). Qed.

Lemma read_bytes_map_read_byte : forall ms a len,
  read_bytes_map (ms_read_byte ms) a len = ms_read_bytes ms a len.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h01ah13lenh22msh31op;1p;3p;6p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0g005<R0p4p710R7p8p1005Zp4p710R8P4p8P8P7p8p10067p4p70R9p1006ep4p7210p8P9P4p8P9p1007Ap4p710p8P9P8p8P9P5p8P9P6p8P9p10087p4p710p8P9p10093p4p710p8P9P7p8P9p1009mp4p710p8p100:Jp4p7210R9P1p8P9P2p8P9P4p8P9P5p8P9P6p8P9p100;6p4p7210p8P9P7p8P9P3p8P9p100;Sp4p710p8p100<]p4p70R9P4p8P9P5p8P9P6p8P9P7p8p100=Sp4p710R9P4p8P9P7p8g00>2j10Tg00>Wj14Tg00?5j12Tg00?Xj15Tg00@8j1=Tg00@Zj1;Tg00Khj1:Tg00A^j36Tg00Lcj33Tg00Cdj31Tg00Mhj37Tg00Nnj38Tg00Okj39TP0j6<Tg00Hbg00JH#0#0#0R0#0#0#0#4#2R7%40#2#5#=R0f2R9#;R4f1R6f0R5#:R336R2f3?3969105X30A7936A39659102eA8465A9465E<X17W0W2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma apply_effect_no_write : forall ms r,
  apply_effect ms (mkEffect r [] []) = set_gpr0 ms r.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h02msh11rp;1p;3p;2p;6p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8p1007Ap4p710p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8p1009mp4p710p8p100:Jp4p7210R8P1p8P8P2p8P8P4p8P8P5p8P8P6p8P8p100;6p4p7210p8P8P0p8P8P3p8P8p100;Sp4p710p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P0p8p100=Sp4p710R8P4p8P8P0p8g00>2j10Tg00>Wj13Tg00?5j15Tg00Pkj17Tg00DXj1PTg00E6j3KTg00QPj34Tg00D>j2>Tg00?Xj1<Tg00ROj22Tg00Roj11Tg00SOj69Tg00TMj1:Tg00UCj1OTg00VBj1NTg00WBj1MTg00XCj1JTg00YIj1HTg00ZHj1BTg00[Gj1?Tg00\Ej1@Tg00]>j2ATg00^7j1=Tg00^oj2CTg00_gj1DTg00``j3ETg00aYj1FTg00bRj2GTg00cKj1;Tg00dIj8ITg00Cdj36Tg00ePj28Tg00fIj2LTg00HbR0g00JH#0R8#0#0R4#0#0#0#3#5R6f1R5%78R8#3%08#Pg00KL3KR8f0R334R2,>0P3%34#5#<,26#11266#1R4P4g00gI#1g00Ii,26#1E9R6#:9458R8#O%N8%M8%J8%H8%B8%?8R4%@6,A4%=6'C%D63E%F6'G%;8GI=602e18561L53560eW1W0o"). Qed.

Lemma apply_effect_copyins_no_write : forall ms r copyins,
  apply_effect ms (with_copyins copyins (mkEffect r [] [])) = set_gpr0 ms r.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h07copyinsh12msh21rp;1p;2p;3p;6p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8p1007Ap4p710p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8p1009mp4p710p8p100:Jp4p7210R8P1p8P8P2p8P8P4p8P8P5p8P8P6p8P8p100;6p4p7210p8P8P0p8P8P3p8P8p100;Sp4p710p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P0p8p100=Sp4p710R8P4p8P8P0p8g00>2j10Tg00>Wj12Tg00?5j15Tg00ROj23Tg00?Xj1=Tg00Pkj1QTg00DXj1MTg00E6j3CTg00QPj3;Tg00D>j2@Tg00Roj11Tg00SOj64Tg00TMj19Tg00aYj1<Tg00^7j1:Tg00\Ej18Tg00_gj17Tg00UCj1PTg00VBj1OTg00WBj1LTg00XCj1KTg00YIj1JTg00ZHj1BTg00[Gj1DTg00]>j2ETg00^oj2ATg00``j3FTg00bRj2GTg00cKj1HTg00dIj8ITg00Cdj36Tg00hAj2?Tg00ePj2>Tg00fIj2NTg00HbR0g00JH#0R8#0#0R4#0#0#0#2#5R6g00Ii,36R5#=f2R3%Q8R8#2%08#Mg00KL3CR8f1R23;R1,@0P2%24#5#=,36#11366#1R6P6g00gI#1%15E4R5#9%<5%:5%85%75f0R6E4R4#99;38R8#P%O8%L8%K8%J8%B8%D8R7%84,E7%:4'A%743F%<4'G%H8GI=601e1?65,>31N32560eW0W2W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_sys_input64 : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h02msh14segsh22x8p;1p;2p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8p1007Ap4p710p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8p1009mp4p710p8p100:Jp4p7210R8P1p8P8P2p8P8P4p8P8P5p8P8P6p8P8p100;6p4p7210p8P8P0p8P8P3p8P8p100;Sp4p710p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P0p8p100=Sp4p710R8P4p8P8P0p8g00?Xj14Tg00>2j10Tg00>Wj12Tg00?5j11Tg00D>j23Tg00i<#4g00Hbg00JH#0#0#0#0#0#0#2#1R0f0,30W2W0W1o"). Qed.
Lemma in_arg0_sys_input64 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h02msh14segsh22x8p;1p;2p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8p1007Ap4p710p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8p1009mp4p710p8p100:Jp4p7210R8P1p8P8P2p8P8P4p8P8P5p8P8P6p8P8p100;6p4p7210p8P8P0p8P8P3p8P8p100;Sp4p710p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P0p8p100=Sp4p710R8P4p8P8P0p8g00?Xj15Tg00>2j10Tg00>Wj12Tg00?5j11Tg00j;j24Tg00D>j23Tg00i<#5g00Hbg00JH#0#0#0#0#0#0#2#1R0f1g00Jm'4,30W2W0W1o"). Qed.
Lemma in_arg1_sys_input64 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h02msh14segsh22x8p;1p;2p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8p1007Ap4p710p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8p1009mp4p710p8p100:Jp4p7210R8P1p8P8P2p8P8P4p8P8P5p8P8P6p8P8p100;6p4p7210p8P8P0p8P8P3p8P8p100;Sp4p710p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P0p8p100=Sp4p710R8P4p8P8P0p8g00?Xj16Tg00>2j10Tg00>Wj12Tg00?5j11Tg00Gbj15Tg00j;j24Tg00D>j23Tg00i<#6g00Hbg00JH#0#0#0#0#0#0#2#1R0f1g00Jm#5'4,30W2W0W1o"). Qed.
Lemma in_arg2_sys_input64 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h02msh14segsh22x8p;1p;2p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8p1007Ap4p710p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8p1009mp4p710p8p100:Jp4p7210R8P1p8P8P2p8P8P4p8P8P5p8P8P6p8P8p100;6p4p7210p8P8P0p8P8P3p8P8p100;Sp4p710p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P0p8p100=Sp4p710R8P4p8P8P0p8g00?Xj16Tg00>2j10Tg00>Wj13Tg00?5j12Tg00Gbj11Tg00j;j25Tg00D>j24Tg00i<#6g00Hbg00JH#0#0#0#0#0#0#3#2R0f1g00Jm#1#1'5,40W2W0W1o"). Qed.
Lemma in_mem_sys_input : forall segs ms x8,
  in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h02msh14segsh22x8p;1p;2p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8p1007Ap4p710p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8p1009mp4p710p8p100:Jp4p7210R8P1p8P8P2p8P8P4p8P8P5p8P8P6p8P8p100;6p4p7210p8P8P0p8P8P3p8P8p100;Sp4p710p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P0p8p100=Sp4p710R8P4p8P8P0p8g00?Xj16Tg00>2j10Tg00>Wj12Tg00?5j11Tg00@8j15Tg00@Zj14Tg00D>j23Tg00i<#6g00Hbg00JH#0#0#0R0#0#0#0#2#1R8%20#1#5\8f1#4'3W2W0W1o"). Qed.

(* [comment removed for export] *)
Lemma syscall_spec_write : forall segs ms x8 model o,
  bv_unsigned x8 = 64%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> write_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
         (sys_input segs ms x8) model o).
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "p'0h03Hnoh15modelh22msh31oh44segsh52x8h61zi001ai011xp;1p;2p;3p;4p;6p-1R0p10000p4p710R1p9P0g00k9R2p4p710R3p9P0p1001?R4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p1001]p4p710R4p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R5p8P0p1004Ap4p710R6p8P0p1004_p4p7210R7p8P0g005<R0p4p710R8p8p1005Zp4p710R9P5p8P9P8p8p10067p4p70R:p1006ep4p7210p8P:P5p8P:p1007Ap4p710p8P:P9p8P:P6p8P:P7p8P:p10087p4p710p8P:p10093p4p710p8P:P8p8P:p1009mp4p710p8p100:Jp4p7210R:P1p8P:P3p8P:P5p8P:P6p8P:P7p8P:p100;6p4p7210p8P:P8p8P:P4p8P:p100;Sp4p710p8p100<]p4p70R:P5p8P:P6p8P:P7p8P:P8p8p100=Sp4p710R:P5p8P:P8p8g00?Xj1CTg00>2j11Tg00>Wj1=Tg00?5j1:Tg00kgj1BTg00l_j24Tg00DXj1>Tg00Cdj3<Tg00mIj2;Tg00nIj32Tg00o?j49Tg010<j48Tg00j;j20Tg0114j17Tg00Gbj16Tg011mj63Tg0131R8j25TP2j4ATP0j6@Tg013Jj3?Tg00i<#Cg00Hbg00JH#1#1#1#1#1#1R0#=R2#:g014Eg015;R:#Bg0169R5f2R7,42%>0R03<P5P0g00@8g016Wp-0R0g017Vf0R6';P6f7f6R4f5R332f4R1f3R9C9P:A2431R4P9P7C8n10110100021010000g00JmR:,03#7%6:R;,03%6;R<,03P4P9P7E3'5X65P0P8g018Z101:#7101;101<A2319R1P7f1R3E3R<CA1429P6E@A?173/5<eW0W3W1W5W2W4o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fd1chan (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
  /\ m_channel_reader model = true.

(* [comment removed for export] *)
Definition buf_modeled (b : list byte) : Prop :=
  (Z.of_nat (length b) <= rw_bytes_max)%Z.

Definition bufs_modeled (bufs : list (list byte)) : Prop :=
  Forall buf_modeled bufs.

(* [comment removed for export] *)
Lemma bufs_modeled_single : forall b, buf_modeled b -> bufs_modeled [b].
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h01Hh11bp;1p;2p;6p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8p1007Ap4p710p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8p1009mp4p710p8p100:Jp4p7210R8P1p8P8P2p8P8P4p8P8P5p8P8P6p8P8p100;6p4p7210p8P8P0p8P8P3p8P8p100;Sp4p710p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P0p8p100=Sp4p710R8P4p8P8P0p8g00>2j10Tg00>Wj17Tg00?5j12Tg00?Xj11Tg019JR0j16Tg00Roj15Tg01:Ij23Tg01:jj64Tg00JH#0#0#0#7#2#1R8f0R4#6P8P0f1%58P41380E4W0W1o"). Qed.

(* [comment removed for export] *)
Lemma buf_modeled_nil : buf_modeled [].
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h01xh17__arithh24__ffh38__varmaph45__with51yp;1p;2p;<p;4p;7p;3p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0g002UR0p4p710p8p10035p4p70R4p1003ep4p710R5p8P4p1004Ap4p710R6p8P4p1004_p4p7210R7p8P4p1005<p4p710R4p8p1005Zp4p710R8P5p8P8P4p8p10067p4p70R9p1006ep4p7210p8P9P5p8P9p1007Ap4p710p8P9P8p8P9P6p8P9P7p8P9p10087p4p710p8P9p10093p4p710p8P9P4p8P9p1009mp4p710p8p100:Jp4p7210R9P1p8P9P2p8P9P5p8P9P6p8P9P7p8P9p100;6p4p7210p8P9P4p8P9P3p8P9p100;Sp4p710p8p100<]p4p70R9P5p8P9P6p8P9P7p8P9P4p8p100=Sp4p710R9P5p8P9P4p8g01;KR4j14Tg00>2j13Tg00DXj17Tg01;kR9j21Tg01<Gj1ITg00D>j22Tg01<el<;Tg00Roj15Tg00?Xj18Tg01=Jj19Tg01=hj1:Tg01>Fj1KTg01?1j26Tg01?Tj4JTg01@?j7HTg01@cj2BTg01AEj2?Tg00Cdj3>Tg01B1j3@Tg01BPj4ATg01CBj4<Tg00>Wj1CTg00?5j1DTP0j2ETg019Jj1FTg01Cml<GTf0R0#3#3p=0g00IiR5g0169R7P7P7P4P4f3f2R4f1R6g00JmR3g01DRR2P0M<Gp==%43R3g00JH#3#0R1#0#0#0#0#0#0#0#7R8'11128R:P7P7P9P0X07R;P91160#IX57X07P3P2P;P;%40,27X051272C=P8P81278M<;g01E0R5#5%85%97%:7%K7R5g01E\g01F;R;P;g01F[R;P71672g01G;1678CJg01GbFH1B5;P0P4g01HBR;g01HbR5'21?04=>;5dA@726CAb2b3b4P:P0b1C<g01IBR0,13e%C1#DR1%51R1'E#4/10e%F1eo"). Qed.

(* A write answers the delivered length, which [buf_modeled] holds at or below
   [rw_bytes_max]; -ENOMEM is just under 2^64, so the answer is never it. *)
Lemma write_ret_not_ENOMEM : forall n (b : list byte),
  buf_modeled b -> bv_eqb (len_word (firstn n b)) (errno_ret ENOMEM) = false.
Proof.
  intros n b Hb. unfold buf_modeled in Hb.
  assert (Hlen : (Z.of_nat (length (firstn n b)) <= rw_bytes_max)%Z)
    by (rewrite length_firstn; lia).
  pose proof (word_unsigned_range (errno_ret ENOMEM)) as Hr.
  assert (He : bv_unsigned (errno_ret ENOMEM) = 18446744073709551604%Z)
    by (vm_compute; reflexivity).
  rewrite He in Hr.
  apply Bool.not_true_is_false. intros Heq.
  apply bv_eqb_eq in Heq. apply (f_equal bv_unsigned) in Heq.
  rewrite (len_word_unsigned (firstn n b)) in Heq
    by (unfold rw_bytes_max in Hlen; lia).
  rewrite He in Heq. unfold rw_bytes_max in Hlen. lia.
Qed.

Lemma buf_modeled_skipn : forall n (b : list byte),
  buf_modeled b -> buf_modeled (skipn n b).
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h01nh11xh24__p1h34__p2h44__x1h54__x2h64__x3h74__x4h81Hh92H1h:7__arithh;4__ffh<8__varmaph=5__with>1bh?4cstrh@5cstr0hA1mhB1yhC2z1p;1p;2p;3p;4p;7p;6p;Bp;<p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0g002UR0p4p710p8p10035p4p70R4p1003ep4p710R5p8P4p1004Ap4p710R6p8P4p1004_p4p7210R7p8P4g005<R4p4p710R8p8p1005Zp4p710R9P5p8P9P8p8p10067p4p70R:p1006ep4p7210p8P:P5p8P:p1007Ap4p710p8P:P9p8P:P6p8P:P7p8P:p10087p4p710p8P:p10093p4p710p8P:P8p8P:p1009mp4p710p8p100:Jp4p7210R:P1p8P:P2p8P:P5p8P:P6p8P:P7p8P:p100;6p4p7210p8P:P8p8P:P3p8P:p100;Sp4p710p8p100<]p4p70R:P5p8P:P6p8P:P7p8P:P8p8g01JCR:p4p710R7P5p8P7P8p8g00>2j1?Tg00>Wj1kTg00?5j1STg00?Xj1GTg019Jj1KTP0j23Tg01Jdj2UTg01;KR0j11Tg01;kR8j20Tg01K;j22Tg01KXj2:Tg01<Gj1LTg00D>j25Tg01L5j1ITg01LZj2WTg01M<j2JTg00Cdj37Tg01MXj2<Tg01N3j2FTg00Gbj1;Tg01NMj28Tg01O6j36Tg01O_j2ETg00Roj1RTg00F>j3DTg01PKj2CTg01=Jj1OTg01Pij4BTg01=hj1NTg01>Fj1MTg01QGj2>Tg00Pkj1PTg01Qjj3QTg01?Tj4@Tg01?1j2iTg01RMj7hTg00G@j1gTg01@cj2bTg01AEj2\Tg01B1j3ZTg01BPj4[Tg01CBj4YTg01S1j3XTP:j3^TP4j6_Tg01SOlB`Tg01Cml<aTg01<el<VTg01T5j6dTg01@?j7eTg01TYj7TTg01U=j8fTg00IiR4P4P4g0169R:P:P:g01UaP0P0P0f6R7g01VAf5R5f4R6f3R3f2R2f1R1f0R9MB`p=jP4P:P:P:P0P0P5P6P3P2P1P9M<ap=cP:P:P8P5P8P6P3P2P1g01IBR8P8P9M<Vp=]P1g01E\R0g01F;R;P;g01F[R<P9Edp=HP1P0P;P;P<P9g01GbFep=4P2P0P;P;P<P1P9FTp=AP:P1g01G;P9C@p==P3P0P;P;P<P2P1P9Gfp=9g00JHR=#?R>#?R?#?#k#SR@#G%K9P413@1RA/U2RB%19RC/08X04%1BRD/08g01DRRE%1ARF%12RG'2':RH/08P9X1:RI1019#LXB:X1:PDPHPIPI15:CX14PBPH1219,:EXA:X0:PAPF15:FP2PG15:GFjEc15:8E]%I210EG13@2RG#I%1G,0E13@3#1%16'2RG,WE1JEG1:EGRF=7:G'<10GEA7:FE'<'F13@6#1%15'2,:EP:p-0RFg01E0RGg00JmRA#;RH#;RB#;RC#;,8:RI18:C18:H18:A56:RA56:56:g01VhRH'E18:B=6:A96:I/EH%RG5DG3D%GGP:P:1C:6P2%O:CBP11C:3CB%N:%M:RGPGP0P;P;P<1HG7P:1>:=R0g01WTRH%P=,>:R=1>:?R?5Q:C@,4G5AGf7RI,HGP:P0PH1i:ERHC@,4G5AGFh%g;R;PG1=H=,4GP;PG1=H?,4GP;PG1>:>R>,==,4GP;1=0>,4GC9C9C9C91bG<P9P2g01HBRGg01HbR<'51\92=7G<dAZ:E1C[b;b<b=X4:X5:X6:X7:X2FW3122397:9,<6A7:9E,<5'F10E310E510561065[[[[^4:^5:^6:^7:^2F^3FP913@7#1R7%1IRI'2R9/0E1JE9PIP7P8P1P2P3P6P5O:b:bCb9b@b?CYAX@21R5,3@A^@21E_%K5eW8W>X04o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma write1_check_n : forall segs ms x8 model buf n,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* THE RANGE [vfs_write]'s [access_ok] ACCEPTS.  The channel arm asks it
     on the named count before it reads the source, so a delivery is
     admissible only there: without this premise the lemma was true of a
     walk that wrapped at 2^64 and is false of one that does not, exactly
     where the buffer leaves the user address space ([buf + count] past
     [State.TASK_SIZE]; [Uaccess.access_okb_intro] gives it from that
     inequality).  A repair of a statement that had become false, not a
     weakening *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  check_write (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (with_copyins [(ms_gpr ms 1, n)]
      (mkEffect (len_word (firstn n buf)) [] [])) model
    = CheckOk model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf)).
Proof.
  intros segs ms x8 model buf n Hfd Hno Hg Hr Hok Hcnt Hn1 Hn2.
  unfold fd1chan in Hfd. destruct Hfd as [Hfd Hrdr].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  unfold check_write.
  rewrite Hg; norm_fd32; rewrite Hfd.
  change (w_is0 (Z_to_bv 64 1)) with false. cbv beta iota.
  rewrite Hmc. cbv beta iota.
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc. cbv beta iota. cbv zeta.
  rewrite Hok. cbn [negb]. cbv beta iota.
  rewrite Hrdr. change (negb true) with false. cbv beta iota.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb).
  assert (Hg0 : Nat.eqb (length buf) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0. cbv beta iota. unfold with_copyins; cbn.
  assert (Hlenf : Z.of_nat (length (firstn n buf)) = Z.of_nat n)
    by (rewrite length_firstn; lia).
  assert (Hru : bv_unsigned (len_word (firstn n buf)) = Z.of_nat n).
  { rewrite (len_word_unsigned (firstn n buf));
      [exact Hlenf | rewrite Hlenf; lia]. }
  rewrite ?Hru.
  assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
  assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length buf))%Z = true)
    by (apply Z.leb_le; lia).
  rewrite ?Hg1, ?Hg2. cbn [andb].
  rewrite ?Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma write1_ok_n : forall segs ms x8 model buf n,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* see [write1_check_n] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (with_copyins [(ms_gpr ms 1, n)]
          (mkEffect (len_word (firstn n buf)) [] [])) model
        (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
Proof.
  intros segs ms x8 model buf n Hfd Hno Hg Hr Hok Hcnt Hn1 Hn2.
  apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
  apply check_write_sound_ok. apply write1_check_n; assumption.
Qed.

(* [comment removed for export] *)
Lemma write1_ok_inv : forall segs ms x8 model eff model' evs buf,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (1 <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    eff = with_copyins [(ms_gpr ms 1, n)]
            (mkEffect (len_word (firstn n buf)) [] []) /\ model' = model /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf).
Proof.
  intros segs ms x8 model eff model' evs buf Hfd Hno Hg Hr Hok Hnb Hspec.
  unfold fd1chan in Hfd. destruct Hfd as [Hfd Hrdr].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply check_write_complete_ok in Hspec.
  unfold check_write in Hspec.
  rewrite Hg in Hspec; norm_fd32; rewrite Hfd in Hspec.
  change (w_is0 (Z_to_bv 64 1)) with false in Hspec. cbv beta iota in Hspec.
  (* being handed [Ok] already rules the transfer-size guard out: had it
     fired, the checker would have answered [CheckUnmodeled] *)
  destruct (negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)));
    cbv beta iota in Hspec; [discriminate|].
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc in Hspec. cbv beta iota zeta in Hspec.
  rewrite Hok in Hspec. cbn [negb] in Hspec. cbv beta iota in Hspec.
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv beta iota in Hspec.
  (* the source the transfer sees is the CLAMPED prefix of the range the
     call named -- [buf] itself for every count under [MAX_RW_COUNT], and
     a prefix of it above, which the gate above admits at an in-range
     buffer *)
  rewrite (write_source_prefix _ _ _ _ Hrb) in Hspec.
  pose proof (rw_count_clamp_range (ms_gpr ms 2)) as Hcl.
  set (c := Z.to_nat (rw_count_clamp (ms_gpr ms 2))) in *.
  assert (Hcpos : (1 <= c)%nat)
    by (unfold c, rw_count_clamp, MAX_RW_COUNT in *; lia).
  assert (Hfl : length (firstn c buf) = Nat.min c (length buf))
    by apply length_firstn.
  assert (Hg0 : Nat.eqb (length (firstn c buf)) 0 = false)
    by (rewrite Hfl; apply Nat.eqb_neq; lia).
  rewrite Hg0 in Hspec. cbv beta iota in Hspec.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length (firstn c buf)))%Z) eqn:Hgr;
    [|discriminate].
  destruct (access_ranges_eqb copyins [(ms_gpr ms 1, Z.to_nat (bv_unsigned ret))])
    eqn:Hreads; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in Hgr as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  rewrite Hfl in H2.
  apply access_ranges_eqb_eq in Hreads. subst copyins.
  exists (Z.to_nat (bv_unsigned ret)).
  assert (Hff : firstn (Z.to_nat (bv_unsigned ret)) (firstn c buf)
                = firstn (Z.to_nat (bv_unsigned ret)) buf)
    by (rewrite firstn_firstn; f_equal; lia).
  rewrite Hff.
  assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) buf) = ret)
    by (apply len_word_firstn_ret; lia).
  rewrite Hlw. repeat split; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma write1_no_unmodeled : forall segs ms x8 model buf,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (* a zero [count] is genuinely unmodeled when the range verdict is
     unclear (see [access_ok_zero] in the write spec), so the nonempty
     buffer is load-bearing here, not just convenient *)
  (1 <= length buf)%nat ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb Hspec.
  unfold fd1chan in Hfd. destruct Hfd as [Hfd Hrdr].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_write in Hspec.
  rewrite Hg in Hspec; norm_fd32; rewrite Hfd in Hspec.
  change (w_is0 (Z_to_bv 64 1)) with false in Hspec. cbv beta iota in Hspec.
  rewrite Hmc in Hspec. cbv beta iota in Hspec.
  destruct (w_is0 (ms_gpr ms 2)) eqn:Hc; try rewrite Hc in Hspec.
  { exfalso.
    assert (Hc0 : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
    congruence. }
  (* [vfs_write]'s [access_ok]: a refused range is -EFAULT, an answer *)
  destruct (negb (access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)))).
  { now apply check_ret_only_no_unmodeled in Hspec. }
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb)
    in Hspec.
  destruct (length buf =? 0)%nat eqn:Hz; try rewrite Hz in Hspec.
  { now apply check_ret_only_no_unmodeled in Hspec. }
  discriminate Hspec.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_prefix_app_mono {A} : forall (l a b : list A),
  is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h01ah11bh21lh31Ah41Hh52IHh61xp;1p;3p;2p;4p;5p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8g007AR9p4p710R:p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8g009mR8p4p710R7p8p100:Jp4p7210R;P1p8P;P2p8P;P4p8P;P5p8P;P6p8P;p100;6p4p7210p8P;P0p8P;P3p8P;p100;Sp4p710p8p200R;P:p8P;g038?R:p4p710p8P;P7p8p100<]p4p70R7P4p8P7P5p8P7P6p8P7P0p8p100=Sp4p710R7P4p8P7P0p8g00?Xj12TP9j31TP8j30Tg00Roj13Tg00Cdj38Tg00D>j27Tg030bj46Tg00F>j34TP:j55Tf0R:#2f1R8%28R9f2R0#2R7f3R4#2R6f4R5?18:f5R3A0340A034831[]1]0W2A148:P:%35R2=050A0528515eW4X17X09%25R9A138:f6R2A0240A024831[]1^06%23A128:f7R2?833A0250A02585121723P4P0P8P:O3C6A4235R3=020A0238512eW4W1X09W5X27X68P:D5W2X3;P:O1X3;o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wevents_ch (ch : word) (bufs : list (list byte)) : list event :=
  match bufs with
  | [] => []
  | buf :: rest => map (WriteEv ch) buf ++ wevents_ch ch rest
  end.

Inductive wpick (ch : word) : list (list byte) -> list event -> Prop :=
| wp_nil : wpick ch [] []
| wp_cons : forall buf bufs n tr,
    (1 <= n)%nat -> (n <= length buf)%nat ->
    wpick ch bufs tr ->
    wpick ch (buf :: bufs) (map (WriteEv ch) (firstn n buf) ++ tr).

(* [comment removed for export] *)
Lemma wpick_wevents : forall ch bufs,
  Forall (fun b => (1 <= length b)%nat) bufs ->
  wpick ch bufs (wevents_ch ch bufs).
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h02Hch11bh24bufsh31Hh42Hbh53Hbsh62IHh72bsh82chh91lp;1p;2p;3p;8p;4p;6p;7p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0g002UR0p4p710p8p10035p4p70R4g003eR5p4p710R6p8P4p1004Ap4p710R7p8P4p1004_p4p7210R8p8P4p1005<p4p710R4p8p1005Zp4p710R9P6p8P9P4p8p10067p4p70R:g006eR;p4p7210p8P:P6p8P:p1007Ap4p710R<p8P:P9p8P:P7p8P:P8p8P:p10087p4p710p8P:p10093p4p710p8P:P4p8P:g009mR:p4p710R9p8p100:Jp4p7210R=P1p8P=P2p8P=P6p8P=P7p8P=P8p8P=p100;6p4p7210p8P=P4p8P=P3p8P=p100;Sp4p710p8p1038ap4p710R=P<p8P=p1038?p4p710p8P=P9p8p100<]p4p70R9P6p8P9P7p8P9P8p8P9P4p8g039gR9p4p710R8P6p8P8P4p8g00>2j12Tg00>Wj1=Tg00?5j1:Tg00?Xj18Tg00Gbj1DTP0j23Tg01Z>j2;Tg03:Fj39Tg03:gj20Tg03;ej31Tg03<`j1@Tg03=[j1?Tg03>?j8>Tg00F>j37Tg01m2j15Tg01f?j3<TP;j46TP:j34TP9j2CTP5j6BTg03?:j7ATg00JH#2#2#2R5#2#2#2#=#:%=5#:R5#8R9#8R:g00Jm#DR;f0R0,35';X19R4=990P9P4f3R81080710X2:f2R6#@f1R7,35,;;A9947f6R41046716f7R;f4R=P8135=R<10;8R3P6%?<P0G>A79=8R8g02YWR6P5P6%5;A<5<=C6;4351;P9f5R3,35=<53f9R<A7943P5P6%5<P0C610<354631X99P0P31C53EBf8R<A793=P5P6%5<P3C610<=54631P0b0b010;891;8eW6W5W4X7:X19P7P0FAW3W2W8o"). Qed.

(* [comment removed for export] *)
Definition wkill_post (fs : Fs.Fs) : post :=
  fun tr o =>
    tr = [KillEv (Z_to_bv 64 SIGPIPE) fs]
    /\ match o with
       | OHalt c => m_killed (cfg_model c) = Some (Z_to_bv 64 SIGPIPE)
       | OError _ => False
       end.

Definition fd1dead (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
  /\ m_channel_reader model = false
  /\ m_sigpipe_default model = true
  /\ m_sigpipe_terminal model = true
  /\ sigpipe_blocked (m_sigmask model) = false.

Lemma write1_dead_check : forall segs ms x8 model eff,
  fd1dead model ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  check_write (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) eff model
  = check_ret_only eff (errno_ret EPIPE)
      (with_killed (Z_to_bv 64 SIGPIPE) model) [].
Proof.
  intros segs ms x8 model eff (Hfd & Hrdr & Hdef & Hterm & Hmask) Hg Hok Hc.
  unfold check_write.
  rewrite Hg; norm_fd32; rewrite Hfd.
  change (w_is0 (Z_to_bv 64 1)) with false. cbv beta iota.
  rewrite (rw_range_of_access_ok _ _ Hok). cbv beta iota.
  rewrite Hc. cbv beta iota.
  rewrite Hrdr. change (negb false) with true. cbv beta iota.
  rewrite Hok. change (negb true) with false. cbv beta iota.
  unfold check_sigpipe_write, sigpipe_declines, raise_sigpipe.
  rewrite Hdef, Hterm, Hmask. reflexivity.
Qed.

Lemma write1_dead_ok : forall segs ms x8 model,
  fd1dead model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret EPIPE) [] [])
        (with_killed (Z_to_bv 64 SIGPIPE) model) []).
Proof.
  intros segs ms x8 model Hd Hno Hg Hok Hc.
  apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
  apply check_write_sound_ok.
  rewrite (write1_dead_check segs ms x8 model _ Hd Hg Hok Hc).
  apply check_ret_only_ok_iff. split; [reflexivity | split; reflexivity].
Qed.

Lemma write1_dead_ok_inv : forall segs ms x8 model eff model' evs,
  fd1dead model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  eff = mkEffect (errno_ret EPIPE) [] []
  /\ model' = with_killed (Z_to_bv 64 SIGPIPE) model /\ evs = [].
Proof.
  intros segs ms x8 model eff model' evs Hd Hno Hg Hok Hc Hspec.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply check_write_complete_ok in Hspec.
  rewrite (write1_dead_check segs ms x8 model eff Hd Hg Hok Hc) in Hspec.
  apply check_ret_only_ok_iff in Hspec. exact Hspec.
Qed.

Lemma write1_dead_no_unmodeled : forall segs ms x8 model,
  fd1dead model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hd Hno Hg Hok Hc Hspec.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  rewrite (write1_dead_check segs ms x8 model _ Hd Hg Hok Hc) in Hspec.
  exact (check_ret_only_no_unmodeled _ _ _ _ Hspec).
Qed.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_wexit : machine_state -> list (list byte) -> word -> Prop :=
| tw_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| tw_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    (* The range [vfs_write]'s [access_ok] accepts.  The donor ported the
       model's [write1_check_n]/[write1_ok_n] WITH this premise (see
       :871/:921, whose own comment calls it "a repair of a statement that had
       become false") but did not port the matching premise onto this
       constructor, so [to_wexit_exec] promised a write [write1_ok_n] will not
       deliver and could not discharge it
       (a build round).  Restored from
       727298f3:theories/Common/CatSim.v's [tw_write].  This NARROWS the
       inductive to the model's own shape; it does not weaken any statement. *)
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit ms (buf :: bufs) code
| tw_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit ms' bufs code ->
    to_wexit ms bufs code.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive msteps : machine_state -> machine_state -> Prop :=
| mst_refl : forall ms, msteps ms ms
| mst_step : forall ms ms' ms'',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    msteps ms' ms'' ->
    msteps ms ms''.

Lemma msteps_one : forall ms ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  msteps ms ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) ["WithSegs"] "h05Hsteph14Hsvch22msh33ms'p;1p;3p;2p;6p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8p1007Ap4p710R9p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8p1009mp4p710R8p8p100:Jp4p7210R7P1p8P7P2p8P7P4p8P7P5p8P7P6p8P7p100;6p4p7210p8P7P0p8P7P3p8P7p100;Sp4p710p8p1038ap6051000R7P9p8P7p1038?p4p710p8P7P8p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P0p8p100=Sp4p710R8P4p8P8P0p8g00>2j10Tg00>Wj1;Tg00?5j13Tg00@8j12Tg00XCj1:Tg00G@j19Tg00Cdj31Tg03?]j14Tg03@ej25Tg03Aaj26Tg03Bij17Tg03Cej68Tg00HbR0g00JH#0#0#0#0#0#0#;#3R8#2f1R4#:%9831%40p,4segsf2R8'5160431f3P8P8P4f0%78E8W0W1X30W2o"). Qed.

Lemma msteps_trans : forall ms ms' ms'',
  msteps ms ms' -> msteps ms' ms'' -> msteps ms ms''.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) ["WithSegs"] "h02msh11Hh23ms'h32H0h42H1h52H2h68IHmstepsh74ms''h85ms''0p;2p;1p;3p;6p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8p1007Ap4p710R9p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8p1009mp4p710R8p8p100:Jp4p7210R7P1p8P7P2p8P7P4p8P7P5p8P7P6p8P7p100;6p4p7210p8P7P0p8P7P3p8P7p100;Sp4p710p8p1038ap6051000R7P9p8P7p1038?p4p710p8P7P8p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P0p8p100=Sp4p710R8P4p8P8P0p8g03Daj20Tg00>2j11Tg00>Wj14Tg00?5j13Tg00@8j1<Tg00XCj1;Tg00G@j1:Tg00Cdj32Tg03?]j15Tg03@ej26Tg03Aaj27Tg03Cej68Tg03E]j69Tg00HbR0f2R8f1R4'0f0R6f3R5'0f4R7,08[X20X001068P6W1X00g00JH#1#1#1#1#1#1#4#3R9#<%;8%:932%50p,4segs/651708321058f7R9,05f5f8R3'0[1073P9f6f9P7P5P4P6O1E8W5W6W4W3W1X80X20X00P5P8P6E9W1X70X20W0o"). Qed.

Lemma msteps_to_wexit : forall ms ms' bufs code,
  msteps ms ms' -> to_wexit ms' bufs code -> to_wexit ms bufs code.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) ["WithSegs"] "h02msh11Hh23ms'h32H0h42H1h52Hwh68IHmstepsh74bufsh84codeh94ms''p;1p;2p;3p;7p;6p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8p1007Ap4p710R9p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8p1009mp4p710R8p8p100:Jp4p7210R7P1p8P7P2p8P7P4p8P7P5p8P7P6p8P7p100;6p4p7210p8P7P0p8P7P3p8P7p100;Sp4p710p8p1038ap6051000R7P9p8P7p1038?p4p710p8P7P8p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P0p8p100=Sp4p710R8P4p8P8P0p8g00>2j11Tg00>Wj15Tg00?5j13Tg00?Xj14Tg03Daj2>Tg03F[j30Tg00@8j1;Tg00XCj18Tg00G@j17Tg00Cdj32Tg03?]j16Tg03@ej29Tg03Aaj2:Tg03GYj7=Tg03E]j6<Tg00HbR0g00JH#1#1#1R8#5#3#4#4%18#1#1#5#3R8f3R4f2R6'>R5f0R7f4R9;04f5R3=069[X20X00A0746P7W1X00%;8%86%7832%60p,4segs/941:0632f8R6f7R8504f9R2=036[A0926P8f6f:P2P9P4f1P7O1F=W5W6X45W3W1X90X20X00P9P4P7E<W1W8W7X20W0o"). Qed.

(* [comment removed for export] *)
Lemma to_wexit_bufs_nonempty : forall ms bufs code,
  to_wexit ms bufs code ->
  Forall (fun b => (1 <= length b)%nat) bufs.
Proof.
  intros ms bufs code H;
    induction H as
      [ms x8 Hsvc Hx8
      | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
      | ms ms' bufs code Hsvc Hstep Hte IH].
  - constructor.
  - constructor; [exact Hnb | apply (IH (length buf)); lia].
  - exact IH.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_write_next_inv : forall ms model x8 buf evs c',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* see [write1_check_n]: on a refused range the step is the -EFAULT *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs (SNext c') ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
    c' = mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model.
Proof.
  intros ms model x8 buf evs c' Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hnb Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
      subst eff model' evs0; exists n
    end.
    match goal with
    | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
        rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
        inversion Hmat; subst model''
    end.
    rewrite apply_effect_copyins_no_write. repeat split; auto.
  - (* sstep_exit : model' halted, but write leaves model unchanged *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite Hh in H6; discriminate
    end.
  - (* sstep_killed : the same, through [State.m_killed_of_m_halted_none] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (m_killed_of_m_halted_none model Hh) in H6;
      discriminate
    end.
Qed.

Lemma sstep_write_inv : forall ms model x8 buf evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
  intros ms model x8 buf evs st Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hcnt Hnb Hss.
  destruct st as [c'|].
  - destruct (sstep_write_next_inv ms model x8 buf evs c'
                Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc').
    exists n. repeat split; [exact Hn1 | exact Hn2 | exact Hevs | now rewrite Hc'].
  - (* SError: only [sstep_syscall_unmodeled] reaches it, and the write
       is modeled *)
    exfalso. inversion Hss; subst; try congruence.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
        Hmat : materialize_model_accesses ?model' _ = None |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf
                    Hfd Hno Hg Hr Hok Hnb H3)
          as (n & _ & _ & _ & Hm & _);
        subst model'; rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
        discriminate
      end.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        apply (write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb H3)
      end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wevents (bufs : list (list byte)) : list event :=
  match bufs with
  | [] => []
  | buf :: rest => map (WriteEv (Z_to_bv 64 1)) buf ++ wevents rest
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wexit_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
  fun tr o =>
    (exists full, wpick (Z_to_bv 64 1) bufs full /\ tr = full ++ [ExitEv code fs])
    /\ exits_with code tr o.

Definition wexit_ready (bufs : list (list byte)) (model : Model) : Prop :=
  bufs = [] \/ fd1chan model.

Lemma to_wexit_exec : forall ms bufs code,
  to_wexit ms bufs code ->
  forall model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  wexit_ready bufs model ->
  bufs_modeled bufs ->
  OmniRun.exec segs (mkCfg ms model) (wexit_post bufs code (m_fs model)).
Proof.
  intros ms bufs code Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfd Hbm.
  - (* tw_exit: the one transition is the exit *)
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
      * unfold wexit_post. cbn beta. rewrite app_nil_r. split.
        -- exists []. split; [apply wp_nil | reflexivity].
        -- cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* tw_write: every delivered length is a successor, each covered by the IH *)
    destruct Hfd as [Hnil | Hfd]; [discriminate Hnil |].
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    apply exec_step; [exact Hh | | |].
    + (* progress: full delivery *)
      eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length buf)]
                  (mkEffect (len_word (firstn (length buf) buf)) [] [])) model model
               (map (WriteEv (Z_to_bv 64 1)) (firstn (length buf) buf))).
      * exact Hh.
      * exact Hsvc.
      * apply write1_ok_n; try assumption. apply Nat.le_refl.
      * exact Hh.
      * rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
    + intros evs Hss.
      destruct (sstep_write_inv ms model x8 buf evs SError
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hb Hnb Hss) as (n & _ & _ & _ & Habs).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_write_inv ms model x8 buf evs (SNext c')
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hb Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
      injection Hc' as ->.
      eapply exec_conseq; [exact (IH n Hn1 Hn2 model Hh Hlazy (or_intror Hfd) Hbs) |].
      intros tr o ((full & Hpick & ->) & Hx). split.
      * exists (map (WriteEv (Z_to_bv 64 1)) (firstn n buf) ++ full).
        split; [apply wp_cons; assumption | apply app_assoc].
      * exact Hx.
  - (* tw_step: one silent instruction *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH model Hh Hlazy Hfd Hbm) |].
      intros tr o H. cbn [app]. exact H.
Qed.

Lemma to_wexit_star_admits : forall ms bufs code,
  to_wexit ms bufs code ->
  forall model full,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  wexit_ready bufs model ->
  bufs_modeled bufs ->
  wpick (Z_to_bv 64 1) bufs full ->
  exists c, star segs (mkCfg ms model) (full ++ [ExitEv code (m_fs model)]) c.
Proof.
  intros ms bufs code Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model full Hh Hlazy Hfd Hbm Hpick.
  - (* tw_exit *)
    inversion Hpick; subst. cbn [app].
    exists (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
    apply star_one.
    replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                     (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
      by (cbn; reflexivity).
    apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
             (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
             (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
    + exact Hh.
    + exact Hsvc.
    + apply (exit_dispatch_ok (sys_input segs ms x8) model).
      rewrite in_sysno_sys_input. exact Hx8.
    + cbn. reflexivity.
    + apply m_killed_with_halted.
  - (* tw_write *)
    destruct Hfd as [Hnil | Hfd]; [discriminate Hnil |].
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    inversion Hpick as [|buf' bufs' n tr Hn1 Hn2 Hpick']; subst.
    destruct (IH n Hn1 Hn2 model tr Hh Hlazy (or_intror Hfd) Hbs Hpick') as [c Hstar].
    exists c. rewrite <- app_assoc.
    eapply star_step; [| exact Hstar].
    rewrite <- (apply_effect_copyins_no_write ms
                  (len_word (firstn n buf)) [(ms_gpr ms 1, n)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model model
             (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + apply write1_ok_n; assumption.
    + exact Hh.
    + rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
  - (* tw_step *)
    destruct (IH model full Hh Hlazy Hfd Hbm Hpick) as [c Hstar].
    exists c.
    replace (full ++ [ExitEv code (m_fs model)])
      with ([] ++ (full ++ [ExitEv code (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_wexit_star_only : forall ms bufs code,
  to_wexit ms bufs code ->
  forall model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  wexit_ready bufs model ->
  bufs_modeled bufs ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    exists full, wpick (Z_to_bv 64 1) bufs full /\
      is_prefix tr (full ++ [ExitEv code (m_fs model)]).
Proof.
  intros ms bufs code Hte model Hh Hlazy Hfd Hbm tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (to_wexit_exec ms bufs code Hte model Hh Hlazy Hfd Hbm) Hstar))
    as (tr' & o & _ & HQ).
  unfold wexit_post in HQ. cbn beta in HQ. destruct HQ as ((full & Hpick & Heq) & _).
  exists full. split; [exact Hpick |]. rewrite <- Heq. apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wexit_no_error : forall ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  wexit_ready bufs model ->
  to_wexit ms bufs code ->
  bufs_modeled bufs ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model bufs code Hh Hlazy Hfd Hte Hbm. apply exec_no_error.
  eapply exec_conseq; [exact (to_wexit_exec ms bufs code Hte model Hh Hlazy Hfd Hbm) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(** The first write the run reaches names a range [access_ok] passes.
    With no reader the channel arm tests the NAMED range before it raises
    the signal ([vfs_write]'s order), and a range past [State.TASK_SIZE]
    answers -EFAULT and lets the run go on, on a return no [to_wexit]
    write node continues from.

    Ported from 727298f3:theories/Common/CatSim.v:965-974, and placed as
    the model places the whole reader-gone block: [wkill_post], [fd1dead]
    and [write1_dead_*] before [Section WithSegs], this inductive and
    [sstep_write_dead_inv], [to_wexit_kill_exec], [to_wexit_kill_obs_iff]
    and [to_wexit_kill_no_error] inside it (they read the section's
    [segs] and its 3-ary [to_wexit]), and the run-level [cat_kill_*]
    lemmas, which bind their own [segs], after it. *)
Inductive wfirst_ok : machine_state -> Prop :=
| wfo_write : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    wfirst_ok ms
| wfo_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    wfirst_ok ms' ->
    wfirst_ok ms.

Lemma sstep_write_dead_inv : forall ms model x8 evs st,
  m_halted model = None ->
  fd1dead model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [KillEv (Z_to_bv 64 SIGPIPE) (m_fs model)]
  /\ st = SNext (mkCfg ms (with_killed (Z_to_bv 64 SIGPIPE) model)).
Proof.
  intros ms model x8 evs st Hh Hd Hsvc Hno Hg Hok Hc Hss.
  inversion Hss; subst; try congruence.
  all: match goal with
       | H2 : ms_svc_pending ?m = Some ?x,
         H3 : syscall_spec (sys_input segs ?m ?x) _ _ |- _ =>
           try (assert (Hx : x = x8) by congruence; subst x)
       end.
  all: match goal with
       | H3 : syscall_spec (sys_input segs ?m ?x) ?mo Unmodeled |- _ =>
           exfalso; exact (write1_dead_no_unmodeled segs m x mo Hd Hno Hg Hok Hc H3)
       | H3 : syscall_spec (sys_input segs ?m ?x) ?mo (Ok ?eff ?model' ?evs0) |- _ =>
           destruct (write1_dead_ok_inv segs m x mo eff model' evs0
                       Hd Hno Hg Hok Hc H3) as (-> & -> & ->)
       end.
  all: rewrite ?m_halted_with_killed, ?m_killed_with_killed in *;
       try discriminate.
  match goal with
  | H : Some _ = Some ?sig |- _ => injection H as Hsig; subst sig
  end.
  split; reflexivity.
Qed.

Lemma to_wexit_kill_exec : forall ms bufs code,
  to_wexit ms bufs code ->
  bufs <> [] ->
  wfirst_ok ms ->
  forall model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1dead model ->
  OmniRun.exec segs (mkCfg ms model) (wkill_post (m_fs model)).
Proof.
  intros ms bufs code Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr _ Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros Hne Hfo model Hh Hlazy Hd.
  - exfalso. exact (Hne eq_refl).
  - (* the first write: signal 13 kills the process *)
    assert (Hok : access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true).
    { inversion Hfo; subst; [assumption | congruence]. }
    assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                    (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
    { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
    pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
    assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
    apply (exec_step_only segs _ _ [KillEv (Z_to_bv 64 SIGPIPE) (m_fs model)]
             (mkCfg ms (with_killed (Z_to_bv 64 SIGPIPE) model))).
    + replace [KillEv (Z_to_bv 64 SIGPIPE) (m_fs model)]
        with ([] ++ [KillEv (Z_to_bv 64 SIGPIPE)
                       (m_fs (with_killed (Z_to_bv 64 SIGPIPE) model))])
        by reflexivity.
      apply (sstep_killed segs ms model x8 (mkEffect (errno_ret EPIPE) [] [])
               (with_killed (Z_to_bv 64 SIGPIPE) model) [] (Z_to_bv 64 SIGPIPE)).
      * exact Hh.
      * exact Hsvc.
      * exact (write1_dead_ok segs ms x8 model Hd Hno Hg Hok Hc).
      * apply m_killed_with_killed.
    + intros evs st Hss.
      exact (sstep_write_dead_inv ms model x8 evs st Hh Hd Hsvc Hno Hg Hok Hc Hss).
    + apply exec_halt.
      * cbn [cfg_model]. rewrite m_halted_with_killed. discriminate.
      * cbv beta. unfold wkill_post.
        split; [rewrite app_nil_r; reflexivity |].
        cbn [cfg_model]. apply m_killed_with_killed.
  - (* a silent instruction: the first write is still ahead *)
    assert (Hfo' : wfirst_ok ms').
    { inversion Hfo; subst; [congruence |].
      match goal with
      | Hs : RiscvSemantics.step segs ms = MachineOk ?m2, Hw : wfirst_ok ?m2 |- _ =>
          rewrite Hstep in Hs; injection Hs as Hm2; subst m2; exact Hw
      end. }
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hne Hfo' model Hh Hlazy Hd) |].
      intros tr o H. cbn [app]. exact H.
Qed.

Lemma to_wexit_kill_obs_iff : forall ms bufs code model,
  to_wexit ms bufs code -> bufs <> [] -> wfirst_ok ms ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1dead model ->
  forall tr, obs_trace segs (mkCfg ms model) tr
             <-> is_prefix tr [KillEv (Z_to_bv 64 SIGPIPE) (m_fs model)].
Proof.
  intros ms bufs code model Hte Hne Hfo Hh Hlazy Hd.
  apply exec_obs_iff.
  eapply exec_conseq;
    [exact (to_wexit_kill_exec ms bufs code Hte Hne Hfo model Hh Hlazy Hd) |].
  intros tr o (Htr & Ho). split; [exact Htr |].
  destruct o; [exact (fun h => h) | destruct Ho].
Qed.

Lemma to_wexit_kill_no_error : forall ms bufs code model,
  to_wexit ms bufs code -> bufs <> [] -> wfirst_ok ms ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1dead model ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms bufs code model Hte Hne Hfo Hh Hlazy Hd. apply exec_no_error.
  eapply exec_conseq;
    [exact (to_wexit_kill_exec ms bufs code Hte Hne Hfo model Hh Hlazy Hd) |].
  intros tr o (_ & Ho). destruct o; [exact (fun h => h) | destruct Ho].
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma init_model_fd1chan : forall reserved brk0 mb sp lim inp,
  in_channel_reader inp = true ->
  fd1chan (init_model reserved brk0 mb sp lim inp).
Proof. intros reserved brk0 mb sp lim inp Hr. split; [reflexivity | exact Hr]. Qed.

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
Definition wexit_launch (bufs : list (list byte)) (inp : ProcInput) : Prop :=
  bufs = [] \/ in_channel_reader inp = true.

Lemma init_model_wexit_ready : forall reserved brk0 mb sp lim inp bufs,
  wexit_launch bufs inp ->
  wexit_ready bufs (init_model reserved brk0 mb sp lim inp).
Proof.
  intros reserved brk0 mb sp lim inp bufs [Hnil | Hr];
    [left; exact Hnil | right; apply init_model_fd1chan; exact Hr].
Qed.

Lemma wexit_ready_with_vdso : forall v m bufs,
  wexit_ready bufs m -> wexit_ready bufs (with_vdso v m).
Proof. intros v m bufs [Hnil | Hr]; [left; exact Hnil | right; exact Hr]. Qed.

Lemma cat_omni_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (wexit_post bufs code (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl.
  cbn [omni_run]. unfold init_config.
  exact (to_wexit_exec (run_segments segs inp sp mb) _ bufs code Hte
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           eq_refl eq_refl
           (wexit_ready_with_vdso _ _ _
              (init_model_wexit_ready
                 (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp
                 lim inp bufs Hl)) Hbm).
Qed.

Lemma cat_obs_iff_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  forall tr, obs_trace (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
             <-> exists full, wpick (Z_to_bv 64 1) bufs full /\
                 is_prefix tr (full ++ [ExitEv code (in_fs inp)]).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl tr.
  set (fs0 := in_fs inp) in *.
  unfold init_config in *.
  set (ms := init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) in *.
  assert (Hh : m_halted (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) = None) by reflexivity.
  assert (Hlazy : m_vm_lazy (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) = []) by reflexivity.
  assert (Hfd : wexit_ready bufs (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)))
    by (apply wexit_ready_with_vdso;
        apply init_model_wexit_ready; exact Hl).
  assert (Hfs : m_fs (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) = fs0) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (to_wexit_star_only (run_segments segs inp sp mb) ms bufs code Hte _ Hh Hlazy Hfd Hbm tr' c Hstar)
      as (full & Hw & Hpref).
    rewrite Hfs in Hpref.
    exists full. split; [exact Hw|].
    eapply is_prefix_trans; eauto.
  - intros (full & Hw & Hp).
    destruct (to_wexit_star_admits (run_segments segs inp sp mb) ms bufs code Hte _ full Hh Hlazy Hfd Hbm Hw)
      as [c Hstar].
    rewrite Hfs in Hstar.
    exists (full ++ [ExitEv code fs0]), c. split; assumption.
Qed.

Lemma cat_no_error_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  ~ reaches_error (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl. apply exec_no_error.
  eapply exec_conseq; [exact (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma cat_must_exit_with_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  must_exit_with code (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl. apply must_exit_with_iff.
  eapply exec_conseq; [exact (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl) |].
  intros tr o (_ & Hx). exact Hx.
Qed.

Lemma cat_omni_run_te_code_unique : forall segs pc ph sp brk0 mb rnd lim inp bufs code code',
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') ->
  code' = code.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code code' Hte Hbm Hl Hex.
  pose proof (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl) as Hrun.
  cbn [omni_run] in Hrun, Hex.
  destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.

Lemma fd1dead_with_vdso : forall v m, fd1dead m -> fd1dead (with_vdso v m).
Proof. intros v m H; exact H. Qed.

Definition sigpipe_fatal (inp : ProcInput) : Prop :=
  in_sigpipe_default inp = true /\ in_sigpipe_terminal inp = true
  /\ sigpipe_blocked (in_sigmask inp) = false.

Lemma init_model_fd1dead : forall reserved brk0 mb sp lim inp,
  in_channel_reader inp = false ->
  sigpipe_fatal inp ->
  fd1dead (init_model reserved brk0 mb sp lim inp).
Proof.
  intros reserved brk0 mb sp lim inp Hr (Hd & Ht & Hm).
  split; [reflexivity | split; [exact Hr | split; [exact Hd | split; [exact Ht | exact Hm]]]].
Qed.

Lemma cat_kill_omni_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
    bufs code ->
  bufs <> [] ->
  wfirst_ok (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  in_channel_reader inp = false ->
  sigpipe_fatal inp ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (wkill_post (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hne Hfo Hr Hm.
  cbn [omni_run]. unfold init_config.
  exact (to_wexit_kill_exec (run_segments segs inp sp mb) _ bufs code Hte Hne Hfo
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           eq_refl eq_refl
           (fd1dead_with_vdso _ _
              (init_model_fd1dead
                 (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp
                 lim inp Hr Hm))).
Qed.

Lemma cat_kill_obs_iff_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
    bufs code ->
  bufs <> [] ->
  wfirst_ok (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  in_channel_reader inp = false ->
  sigpipe_fatal inp ->
  forall tr, obs_trace (run_segments segs inp sp mb)
               (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr [KillEv (Z_to_bv 64 SIGPIPE) (in_fs inp)].
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hne Hfo Hr Hm tr.
  unfold init_config.
  exact (to_wexit_kill_obs_iff (run_segments segs inp sp mb) _ bufs code
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           Hte Hne Hfo eq_refl eq_refl
           (fd1dead_with_vdso _ _
              (init_model_fd1dead
                 (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp
                 lim inp Hr Hm)) tr).
Qed.

Lemma cat_kill_no_error_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
    bufs code ->
  bufs <> [] ->
  wfirst_ok (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  in_channel_reader inp = false ->
  sigpipe_fatal inp ->
  ~ reaches_error (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hne Hfo Hr Hm.
  unfold init_config.
  exact (to_wexit_kill_no_error (run_segments segs inp sp mb) _ bufs code
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           Hte Hne Hfo eq_refl eq_refl
           (fd1dead_with_vdso _ _
              (init_model_fd1dead
                 (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp
                 lim inp Hr Hm))).
Qed.

Definition cat_launch (source_segs : list Segment) (ms_source : machine_state)
    (target_segs : list Segment) (ms_target : machine_state)
    (bufs : list (list byte)) (inp : ProcInput) : Prop :=
  wexit_launch bufs inp
  \/ (sigpipe_fatal inp
      /\ wfirst_ok source_segs ms_source /\ wfirst_ok target_segs ms_target).

Lemma cat_launch_cases : forall source_segs ms_source target_segs ms_target bufs inp,
  cat_launch source_segs ms_source target_segs ms_target bufs inp ->
  wexit_launch bufs inp
  \/ (bufs <> [] /\ in_channel_reader inp = false
      /\ sigpipe_fatal inp
      /\ wfirst_ok source_segs ms_source /\ wfirst_ok target_segs ms_target).
Proof.
  intros source_segs ms_source target_segs ms_target bufs inp
    [Hw | (Hm & Hfs & Hft)]; [left; exact Hw |].
  destruct bufs as [| b bs]; [left; left; reflexivity |].
  destruct (in_channel_reader inp) eqn:Hr; [left; right; exact Hr |].
  right. split; [discriminate |].
  split; [reflexivity | split; [exact Hm | split; [exact Hfs | exact Hft]]].
Qed.

Lemma cat_omni_strong_equiv_te :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) bufs code ->
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) bufs code ->
  bufs_modeled bufs ->
  cat_launch (run_segments source_segs inp rsp rmb)
             (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
             (run_segments target_segs inp asp amb)
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             bufs inp ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
    Hsource Htarget Hbm Hl.
  destruct (cat_launch_cases _ _ _ _ _ _ Hl) as [Hw | (Hne & Hr & Hm & Hfs & Hft)].
  - (* a reader, or no write: both runs exit after the same deliveries *)
    split.
    { cbn [img_segments].
      eapply coexec_conseq;
        [apply exec_coexec;
         exact (cat_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code Hsource Hbm Hw) |].
      intros tr o (_ & Hx).
      exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
    right. split.
    + apply trace_equiv_iff_omni. intro tr. cbn.
      rewrite (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code Hsource Hbm Hw tr).
      rewrite (cat_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code Htarget Hbm Hw tr).
      reflexivity.
    + apply bh_errors_iff. cbn.
      apply (cat_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code Htarget Hbm Hw).
  - (* no reader, signal 13 open: both runs die at their first write *)
    split.
    { cbn [img_segments].
      eapply coexec_conseq;
        [apply exec_coexec;
         exact (cat_kill_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code
                  Hsource Hne Hfs Hr Hm) |].
      intros tr o (_ & Ho). apply never_errors_covered.
      destruct o; [exact (fun h => h) | destruct Ho]. }
    right. split.
    + apply trace_equiv_iff_omni. intro tr. cbn.
      rewrite (cat_kill_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code
                 Hsource Hne Hfs Hr Hm tr).
      rewrite (cat_kill_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code
                 Htarget Hne Hft Hr Hm tr).
      reflexivity.
    + apply bh_errors_iff. cbn.
      apply (cat_kill_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code
               Htarget Hne Hft Hr Hm).
Qed.

(* [comment removed for export] *)
Lemma cat_strong_equiv_te :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) bufs code ->
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) bufs code ->
  bufs_modeled bufs ->
  cat_launch (run_segments source_segs inp rsp rmb)
             (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
             (run_segments target_segs inp asp amb)
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             bufs inp ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp
    Hsource Htarget Hbm Hl.
  destruct (cat_launch_cases _ _ _ _ _ _ Hl) as [Hw | (Hne & Hr & Hm & Hfs & Hft)].
  - split.
    { apply no_error_run_modeled.
      apply (cat_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm Hw). }
    right. split.
    + intro tr. cbn.
      rewrite (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm Hw tr).
      rewrite (cat_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm Hw tr).
      reflexivity.
    + cbn. apply (cat_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm Hw).
  - split.
    { apply no_error_run_modeled.
      apply (cat_kill_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
               Hsource Hne Hfs Hr Hm). }
    right. split.
    + intro tr. cbn.
      rewrite (cat_kill_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
                 Hsource Hne Hfs Hr Hm tr).
      rewrite (cat_kill_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bufs code
                 Htarget Hne Hft Hr Hm tr).
      reflexivity.
    + cbn. apply (cat_kill_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bufs code
                    Htarget Hne Hft Hr Hm).
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
Definition fdchan (fd ch : word) (model : Model) : Prop :=
  fd_lookup (m_fds model) fd = Some (FdChannel ch) /\ w_is0 ch = false
  /\ m_channel_reader model = true.

Lemma fd1chan_fdchan : forall model,
  fd1chan model -> fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model.
Proof.
  intros model [H Hr]. split; [exact H | split; [reflexivity | exact Hr]].
Qed.

Lemma init_model_fdchan2 : forall reserved brk0 mb sp lim inp,
  in_channel_reader inp = true ->
  fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) (init_model reserved brk0 mb sp lim inp).
Proof.
  intros reserved brk0 mb sp lim inp Hr.
  split; [reflexivity | split; [reflexivity | exact Hr]].
Qed.

Lemma write_ch_check_n : forall segs ms x8 model fd ch buf n,
  fdchan fd ch model ->
  fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* see [write1_check_n] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  check_write (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (with_copyins [(ms_gpr ms 1, n)]
      (mkEffect (len_word (firstn n buf)) [] [])) model
    = CheckOk model (map (WriteEv ch) (firstn n buf)).
Proof.
  intros segs ms x8 model fd ch buf n [Hfd [Hch Hrdr]] H32 Hno Hg Hr Hok Hcnt Hn1 Hn2.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  unfold check_write.
  rewrite Hg, H32, Hfd, Hch. cbv beta iota.
  rewrite Hmc. cbv beta iota.
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc. cbv beta iota. cbv zeta.
  rewrite Hok. cbn [negb]. cbv beta iota.
  rewrite Hrdr. change (negb true) with false. cbv beta iota.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb).
  assert (Hg0 : Nat.eqb (length buf) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0. cbv beta iota. unfold with_copyins; cbn.
  assert (Hlenf : Z.of_nat (length (firstn n buf)) = Z.of_nat n)
    by (rewrite length_firstn; lia).
  assert (Hru : bv_unsigned (len_word (firstn n buf)) = Z.of_nat n).
  { rewrite (len_word_unsigned (firstn n buf));
      [exact Hlenf | rewrite Hlenf; lia]. }
  rewrite ?Hru.
  assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
  assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length buf))%Z = true)
    by (apply Z.leb_le; lia).
  rewrite ?Hg1, ?Hg2. cbn [andb].
  rewrite ?Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

Lemma write_ch_ok_n : forall segs ms x8 model fd ch buf n,
  fdchan fd ch model -> fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (with_copyins [(ms_gpr ms 1, n)]
          (mkEffect (len_word (firstn n buf)) [] [])) model
        (map (WriteEv ch) (firstn n buf))).
Proof.
  intros segs ms x8 model fd ch buf n Hfdc H32 Hno Hg Hr Hok Hcnt Hn1 Hn2.
  apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
  apply check_write_sound_ok. eapply write_ch_check_n; eassumption.
Qed.

Lemma write_ch_ok_inv : forall segs ms x8 model fd ch eff model' evs buf,
  fdchan fd ch model -> fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* see [write1_ok_inv] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (1 <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    eff = with_copyins [(ms_gpr ms 1, n)]
            (mkEffect (len_word (firstn n buf)) [] []) /\ model' = model /\
    evs = map (WriteEv ch) (firstn n buf).
Proof.
  intros segs ms x8 model fd ch eff model' evs buf Hfdc H32 Hno Hg Hr Hok Hnb Hspec.
  destruct Hfdc as [Hfd [Hch Hrdr]].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply check_write_complete_ok in Hspec.
  unfold check_write in Hspec.
  rewrite Hg, H32, Hfd, Hch in Hspec. cbv beta iota in Hspec.
  (* see [write1_ok_inv]: [Ok] rules the guard out *)
  destruct (negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)));
    cbv beta iota in Hspec; [discriminate|].
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc in Hspec. cbv beta iota zeta in Hspec.
  rewrite Hok in Hspec. cbn [negb] in Hspec. cbv beta iota in Hspec.
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv beta iota in Hspec.
  (* the source the transfer sees is the CLAMPED prefix of the range the
     call named -- [buf] itself for every count under [MAX_RW_COUNT], and
     a prefix of it above, which the gate above admits at an in-range
     buffer *)
  rewrite (write_source_prefix _ _ _ _ Hrb) in Hspec.
  pose proof (rw_count_clamp_range (ms_gpr ms 2)) as Hcl.
  set (c := Z.to_nat (rw_count_clamp (ms_gpr ms 2))) in *.
  assert (Hcpos : (1 <= c)%nat)
    by (unfold c, rw_count_clamp, MAX_RW_COUNT in *; lia).
  assert (Hfl : length (firstn c buf) = Nat.min c (length buf))
    by apply length_firstn.
  assert (Hg0 : Nat.eqb (length (firstn c buf)) 0 = false)
    by (rewrite Hfl; apply Nat.eqb_neq; lia).
  rewrite Hg0 in Hspec. cbv beta iota in Hspec.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length (firstn c buf)))%Z) eqn:Hgr;
    [|discriminate].
  destruct (access_ranges_eqb copyins [(ms_gpr ms 1, Z.to_nat (bv_unsigned ret))])
    eqn:Hreads; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in Hgr as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  rewrite Hfl in H2.
  apply access_ranges_eqb_eq in Hreads. subst copyins.
  exists (Z.to_nat (bv_unsigned ret)).
  assert (Hff : firstn (Z.to_nat (bv_unsigned ret)) (firstn c buf)
                = firstn (Z.to_nat (bv_unsigned ret)) buf)
    by (rewrite firstn_firstn; f_equal; lia).
  rewrite Hff.
  assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) buf) = ret)
    by (apply len_word_firstn_ret; lia).
  rewrite Hlw. repeat split; try reflexivity; lia.
Qed.

Lemma write_ch_no_unmodeled : forall segs ms x8 model fd ch buf,
  fdchan fd ch model -> fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (* see [write1_no_unmodeled]: a zero [count] is genuinely unmodeled *)
  (1 <= length buf)%nat ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model fd ch buf [Hfd [Hch Hrdr]] H32 Hno Hg Hr Hcnt Hnb Hspec.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_write in Hspec.
  rewrite Hg, H32, Hfd, Hch in Hspec. cbv beta iota in Hspec.
  rewrite Hmc in Hspec. cbv beta iota in Hspec.
  destruct (w_is0 (ms_gpr ms 2)) eqn:Hc; try rewrite Hc in Hspec.
  { exfalso.
    assert (Hc0 : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
    congruence. }
  (* [vfs_write]'s [access_ok]: a refused range is -EFAULT, an answer *)
  destruct (negb (access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)))).
  { now apply check_ret_only_no_unmodeled in Hspec. }
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb)
    in Hspec.
  destruct (length buf =? 0)%nat eqn:Hz; try rewrite Hz in Hspec.
  { now apply check_ret_only_no_unmodeled in Hspec. }
  discriminate Hspec.
Qed.

Section WithSegsCh.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable fd ch : word.

(* [comment removed for export] *)
Inductive to_wexit_ch : machine_state -> list (list byte) -> word -> Prop :=
| twc_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit_ch ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twc_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    (* The [twc_write] half of the same restoration; see [tw_write] above.
       727298f3:theories/Common/CatSim.v, [twc_write]. *)
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit_ch (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit_ch ms (buf :: bufs) code
| twc_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit_ch ms' bufs code ->
    to_wexit_ch ms bufs code.

Lemma msteps_to_wexit_ch : forall ms ms' bufs code,
  msteps segs ms ms' -> to_wexit_ch ms' bufs code -> to_wexit_ch ms bufs code.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) ["WithSegsCh"] "h02msh11Hh23ms'h32H0h42H1h52Hwh68IHmstepsh74bufsh84codeh94ms''p;1p;3p;2p;7p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0p1005<p4p710R0p8p1005Zp4p710R7P4p8P7P0p8p10067p4p70R8p1006ep4p7210p8P8P4p8P8p1007Ap4p710R9p8P8P7p8P8P5p8P8P6p8P8p10087p4p710p8P8p10093p4p710p8P8P0p8P8p1009mp4p710R8p8p100:Jp4p7210R7P1p8P7P2p8P7P4p8P7P5p8P7P6p8P7p100;6p4p7210p8P7P0p8P7P3p8P7p100;Sp4p710p8p1038ap6051000R7P9p8P7p1038?p4p710p8P7P8p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P0p8p100=Sp4p710R8P4p8P8P0p8g00>2j11Tg00>Wj15Tg00?5j13Tg00?Xj14Tg03Daj3>Tg05;5j30Tg00@8j1;Tg00XCj18Tg00G@j17Tg00Cdj32Tg03?]j16Tg03@ej29Tg03Aaj2:Tg05<6j7=Tg03E]j7<Tg00HbR0g00JH#1#1#1R8#5#3#4#4%18#1#1#5#3R8p,4segsR4f3R6f2R53>R7P4f0R9f4R3;06f5R2=053[X20X00A0965P9W1X00%;8%85%7832%6019461:0532f8R5f7R4506f9R8=025[A0385P4f6f:P8P3P6f1P9O1F=W5W6X47W3W1X90X20X00P3P6P9F<W1W8W7X20W0o"). Qed.

Hypothesis Hfd32 : fd32 fd = fd.

Lemma sstep_write_ch_inv : forall ms model x8 buf evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv ch) (firstn n buf) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
  intros ms model x8 buf evs st Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hcnt Hnb Hss.
  revert Hg Hfdc. inversion Hss; subst; intros Hg Hfdc; try congruence.
  - match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hok Hnb H3)
        as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
      subst eff model' evs0; exists n
    end.
    match goal with
    | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
        rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
        inversion Hmat; subst model''
    end.
    rewrite apply_effect_copyins_no_write. repeat split; auto.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf
                  Hfdc Hfd32 Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
      discriminate
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite Hh in H6; discriminate
    end.
  - (* sstep_killed: the write arm hands back the model it was given, and
       a running model is not a killed one *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (m_killed_of_m_halted_none model Hh) in H6;
      discriminate
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      apply (write_ch_no_unmodeled segs ms x8 model fd ch buf Hfdc Hfd32 Hno Hg Hr Hcnt Hnb H3)
    end.
Qed.

End WithSegsCh.

(* [comment removed for export] *)
Lemma to_wexit_ch_1 : forall segs ms bufs code,
  to_wexit segs ms bufs code ->
  to_wexit_ch segs (Z_to_bv 64 1) ms bufs code.
Proof.
  (* 727298f3:theories/Common/CatSim.v, [to_wexit_ch_1]: the recorded term
     applied [twc_write] without the [access_okb] premise its constructor
     carries at the revision (and [tw_write] gives). *)
  intros segs ms bufs code H; induction H.
  - eapply twc_exit; eassumption.
  - eapply twc_write; eassumption.
  - eapply twc_step; eassumption.
Qed.

Lemma wevents_ch_1 : forall bufs, wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
ltac2:(KReplay.run1 (kr_t_CatSim ()) [] "h04bufsh12IHh21bh32bsh41lp;1p;2p;3p;4p;6p;5p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]p4p710R3p9P0p1002Up4p710p8p10035p4p70R0p1003ep4p710R4p8P0p1004Ap4p710R5p8P0p1004_p4p7210R6p8P0g005<R0p4p710R7p8p1005Zp4p710R8P4p8P8P7p8p10067p4p70R9g006eR:p4p7210p8P9P4p8P9p1007Ap4p710R;p8P9P8p8P9P5p8P9P6p8P9p10087p4p710p8P9p10093p4p710p8P9P7p8P9g009mR9p4p710R8p8p100:Jp4p7210R<P1p8P<P2p8P<P4p8P<P5p8P<P6p8P<p100;6p4p7210p8P<P7p8P<P3p8P<p100;Sp4p710p8p1038ap4p710R<P;p8P<g038?R;p4p710p8P<P8p8p100<]p4p70R8P4p8P8P5p8P8P6p8P8P7p8p100=Sp4p710R8P4p8P8P7p8g00>2j10Tg00>Wj19Tg00?5j1;Tg00?Xj14Tg00DXj1@Tg01YXj2<Tg03:gj23Tg05AEj11Tg00Cdj32Tg00Roj18Tg00D>j26Tg01m2j1:TP:j47TP9j35TP0j6?Tg00F>j3>TP;j5=Tg00JHR;#0#0#0R0#9#;R9#4R:#4R7P:g02YWR8#4R4%00#0#0#9%@;'<R;f0R0'3%1032R6X07%88,64%8:R5,3;%15524eP4f1R5#1R<P9P8%:;R3f3C7R2=580f2R1#19582524X44P9P8P3P1C7=58<,6413;5P0E?A>:15R1,3;%11524eX16X37X2:P0D=W0o"). Qed.

End CatSim.
