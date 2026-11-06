(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import SimInv ExitSim CatSim PropExec SeqExec CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_WallSim () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsBpointwise_relationC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib7Classes;EquivalenceEpointwise_equivalenceC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List:Proper_mapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List:firstn_nilI45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC47Corelib4Init9Datatypes6lengthI47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=Z_to_bv_smallC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List@firstn_length_leC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAlen_word_unsignedC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z6inj_leC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC59OSSVerify5KrLib2AS8PropExec5v_addC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions?bv_add_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib2AS7WallSimClen_word_firstn_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7WallSimAu_len_word_firstnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_subC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List<length_skipnC59OSSVerify5KrLib2AS8PropExec;v_sub_smallC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib2AS6CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib2AS7WallSim7to_wall10C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01k59OSSVerify5KrLib2AS7WallSim7to_wall13C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim:msteps_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K59OSSVerify5KrLib2AS6CatSim6msteps01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01i59OSSVerify5KrLib2AS7WallSim7to_wall00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7WallSim@to_wall_tail_indC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib2AS6CatSim6fdchanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim;buf_modeledC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K4ELinuxProcessSemantics?LinuxProcessSem5State5event02K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC59OSSVerify5KrLib2AS6CatSimBsstep_write_ch_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c59OSSVerify5KrLib2AS7WallSimAsstep_to_wall_invC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C56Stdlib5Arith8PeanoNat3Nat7le_reflC59OSSVerify5KrLib2AS6CatSimAbuf_modeled_skipnC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00C46Stdlib5Lists4List9skipn_allC46Stdlib5Lists4List:firstn_allK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC59OSSVerify5KrLib2AS6CatSim=write_ch_ok_nC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04C59OSSVerify5KrLib2AS6CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run4star02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepC4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01c59OSSVerify5KrLib2AS7WallSim>to_wall_mutindC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00c59OSSVerify5KrLib2AS7WallSimGto_wall_star_admits_mutC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClassesEEquivalence_ReflexiveC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib5Lists4List<firstn_skipnC46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List7map_appC59OSSVerify5KrLib2AS7ExitSim?sstep_instr_invC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_Reflexivec59OSSVerify5KrLib2AS7WallSimEto_wall_star_only_mutC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC59OSSVerify5KrLib2AS8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC59OSSVerify5KrLib2AS7CatExec7adv_setC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7WallSim7to_wall01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7WallSim@to_wall_k_ex_mutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7WallSim;to_wallexitC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01c59OSSVerify5KrLib2AS7WallSimAto_wall_tail_k_exC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C47Corelib4Init9Datatypes8list_indK59OSSVerify5KrLib2AS6CatSim8to_wexit03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim?msteps_to_wexitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7WallSimCmsteps_to_wall_tailC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec00K4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome02C47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_conseqK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec02C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun>exec_step_onlyC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4postI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome00I59OSSVerify5KrLib2AS6CatSim8to_wexit00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib2AS7ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC59OSSVerify5KrLib2AS7ExitSimBin_sysno_sys_inputC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7ExitSim@exit_dispatch_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_killed_with_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep06C59OSSVerify5KrLib2AS7ExitSim>sstep_exit_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_halted_with_haltedC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7outcome01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exits_withC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC46Stdlib5Lists4List9app_nil_rK4ELinuxProcessSemantics?LinuxProcessSem7OmniRun4exec01C59OSSVerify5KrLib2AS6CatSim<to_wexit_indC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03c59OSSVerify5KrLib2AS7WallSimEto_wexit_nil_exec_auxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim<bufs_modeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7WallSimAto_wexit_nil_execC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffc59OSSVerify5KrLib2AS7WallSim@to_wall_exec_mutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim:wevents_chC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib2AS7WallSim@to_wallexit_execC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_realizesI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun5mexec00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun?mexec_halt_starC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:exec_soundC47Corelib4Init5Logic6eq_symI4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6cosafe00c59OSSVerify5KrLib2AS7WallSimGto_wallexit_star_admitsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;cosafe_starC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun9exec_starC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunGexits_with_never_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=exec_no_errorC59OSSVerify5KrLib2AS6CatSim7weventsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateC4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun8omni_runI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun8is_errorc59OSSVerify5KrLib2AS7WallSim=wall_omni_runC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<exec_obs_iffC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<img_segmentsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:omni_corunC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence:omni_equivC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun;exec_coexecC4ELinuxProcessSemantics?LinuxProcessSem7OmniRunDnever_errors_coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=coexec_conseqC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence@omni_trace_equivC4ELinuxProcessSemantics?LinuxProcessSem3Run3runC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalenceDtrace_equiv_iff_omniC4ELinuxProcessSemantics?LinuxProcessSem3Run9obs_traceC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc59OSSVerify5KrLib2AS7WallSim<wall_obs_iffC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errorsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=bh_errors_iffc59OSSVerify5KrLib2AS7WallSimAwall_no_error_runC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitK47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitc59OSSVerify5KrLib2AS7WallSim6fd32_1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun6errorsI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_ReflexiveC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence7modeledC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence5equivC59OSSVerify5KrLib2AS6SimInvDno_error_run_modeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=bh_all_errors".
(* [comment removed for export] *)
Unset Lia Cache.

Import ListNotations.
Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}.


(* [comment removed for export] *)
Lemma fd32_1 : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710R0p9p1003Ip4p70R5p10049p4p710R6p8P5p1004Up4p710R7p8P5p10053p4p7210R8p8P5p1005Pp4p710R5p8p1005np4p710R9P6p8P9P5p8p1006Kp4p70R:P1p8P:P2p8P:p10079p4p7210p8P:P6p8P:p1007Up4p7210p8P:P9p8P:P7p8P:P8p8P:P4p8P:P3p4p710p8P:p1008Dp4p710p8P:P5p8P:p10094p4p7210p8P:P0p8P:p1009hp4p710p8P:p100:Ep4p7210R0p8P:p100:bp4p7210p8p100;Ap4p7210R:P6p8P:P7p8P:P8p8P:P5p8p100;mp4p70R:P6p8P:P7p8P:P8p8P:P5p8P0P5p8p100<cp4p710P5p8g00=Bj13Tg00=ej31Tg00>?j20Tg00>ij34Tg00?Mj12Tg00@2j19Tg00@Pj18Tg00@nj25Tg00ATj16Tg00BMj27Tg00BgR5f0R0#3R:f1R8#3R7g00CEf2R6#3?180g00C`R3f3R4/06104831R9[10681060513%34?168[R2f4#3?146\9A4680P0n2001000000120000000W1W0W2P2^17^0:^25P0g00D>R0#2#2#2#2#2#2#9R5%80R0,55R:#6R7P:17301057105:513dO4b3o"). Qed.

Lemma fd32_2 : fd32 (Z_to_bv 64 2) = Z_to_bv 64 2.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h02b1h12b2h21nh31Hp;1p;3p;2g00=Bj13Tg00=ej31Tg00>?j20Tg00>ij34Tg00?Mj12Tg00@2j19Tg00@Pj18Tg00@nj25Tg00ATj16Tg00BMj27Tg00BgR0f0R1#3R2f1R3#3R4g00CEf2R5#3?131g00C`R6f3R7/05107331R8[10531051516%37?153[R9f4#3?175\8A4531P1n2001000000120000000W1W0W2P9^14^02^20P1g00D>#2R1#2#2#2#2#2#9R0%81R1,50R2#6R4P2176110041002516dO4b3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h02Hah14__x1h21Ah31Hh47__arithh54__ffh66__sat0h76__sat1h88__varmaph95__with:4cstrh;1lp;1p;2p;3p;4p;7p;8p200R0g00DcR1p4p710p8P0g00E[R2p4p710p8g00F;j1;TP2j23Tg00F[j14Tg00?Mj12Tg00@Pj1<Tg00G;j2LTg00GXj20Tg00@2j1DTg00H4j1BTg00HYj2@Tg00IAj3>Tg00Iej1=Tg00JEj2UTg00Jcj1TTg00KAj1STg00Klj2:Tg00LOj2KTg00M2j47Tg00M]j1ITg00N?j3HTg00Nbj7CTg00OFj2ETg00BMj2FTg00Ohj2GTg00=ej38Tg00PTj3ATg00Q3j4JTg00CEj25Tg00Qej1?Tg00RNj3MTP1j2NTg00>?j2OTg00S:j2PTg00SVj7QTg00T:j8RTg00T^R1f0R2'Pp=1f1R3g00U<R4g00U[R5P5g00V;R6P2g00V[FQp=9f3R7P4P5P5P6f2R8P3P2GRp=6%;21332#4g00D>R9#2R:#<R;%2:#2#2#2#2R:#<R<'LR='0%D:R:1383R>#4R?%B>%1?R>1@;<101;%1<101=[[%1;R@g00W;RAA>;<3UW0%1=\A^0@g00C`R@g00WWRA#=%;A1U@3%T@%S@RAP@1:@1g00XC1K@9R9C7,9AR<%I5RBPAP@P9g00Xj1:@;=H@:C7,9AR;PBPAP4P5P5P6P<P;FCC6C61EA6P2P8g00YQRAg00Z1R6'F1G28=8A6dAA@13CJb5b8b9W1%12103=%18108='5[[^1@P2f6f5'3#4P7f4O3b4b6b7b:%?:,0?,5>e3M1N83,O:=8@?eW3W;X20o"). Qed.

(* [comment removed for export] *)

Lemma len_word_firstn_nat : forall n (bs : list byte),
  (n <= length bs)%nat ->
  len_word (firstn n bs) = nat_to_word n.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h01nh12Hnh22bsp;1p;2p;3p;4p;6g00?Mj10Tg00@2j15Tg00=Bj13Tg00F;j17Tg00E[j26Tg00ZQj2<Tg00F[j11Tg00@nj22Tg00=ej34Tg00BMj2;Tg00Zkj38Tg00[Jj49Tg005Pj6:Tg00Dcj2>Tg00[oj1=Tg00\jR0g00D>#0#0#0R1#5#3R2#7f1R3f0R4,62'<P0f2R5%01#0#0#5R1#3R6%14,21f3#1,2134X00%15,21,;6A8253R1,62P2P3P5P4C9E:1>21%=5546eW1W2W0o"). Qed.

Lemma u_len_word_firstn : forall n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  bv_unsigned (len_word (firstn n bs)) = Z.of_nat n.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h01nh12Hah24__x1h34__x2h44Hlenh52Hnh63Hn0h77__arithh84__ffh96__sat1h:6__sat2h;8__varmaph<5__with=2bsh>4cstrh?5cstr0h@1zp;1p;2p;3p;4p;6p;<p;7p;8g00?Mj14Tg00@2j1BTg00=Bj1PTg00F;j1>Tg00E[j22Tg00ZQR0j2ATg00F[R1j10Tg00@Pj1?Tg00G;j2LTg00GXj23Tg00Zkj3FTg00=ej36Tg00BMj28Tg00[Jj4`Tg005Pj6:Tg00Dcj2WTg00>?j2VTg00S:R2j21Tg00]Ij4RTg00H4j1@Tg00HYj2QTg00IAj3OTg00^0j1<Tg00^Oj27Tg00_8j3=Tg00_aj2KTg00Iej1HTg00`Mj3GTg00JEj2ITg00`mj1JTg00aKj4ETg00Jcj1MTg00KAj1NTg00LOj2;Tg00M2j49Tg00M]j1DTg00Klj2STg00N?j3TTg00OFj2_Tg00Ohj2^Tg00PTj3]Tg00Q3j4\Tg00aij3XTg00c6l<YTg00SVj7ZTg00T:j8[Tg00\jR3g00C`R4P0P1P2g00c[f5R2f4R1f3R0f2R5f1R6f0R7M<Yp=UP6g00U<R8g00U[R9P9g00V;R:P7g00V[FZp=5P0P8P9P9P:P5P6P7G[p=Cg00D>R8#4R;#4#4R<#B#PR=#>12=7,A612=6#0%?;R>%4<#4#4R<#?R?'LR@'3P4AF=05RA,2=RB#0%01R19647X@4P3P0%07RC=641X03%00R1,84RDPBP=P5P0P6C`REE:%B<R<1W=A'VP3P0g00d=RF,3CX0312=5RC,A0%0CRG,11RHP0P1PDPCPG184GEUP6CRPH12=0R0#@g00T^RH%00'1%@2%02,1H1Q>?13H>11H?13H@[[11H>R0g00W;RGAO>?6UW111H@\G^10g00WWR0g00e6RG#<R?#<,74174?174G5=45=4g00eU'K%H03G%>0P41I45P6%J4CE%M4%N4R0P41;48R8g00XC1;4;R;C9,50%D9R9P0P4P;g00XjR;1S4>=T4<R<C9,50P9P4P8P;P<C9,50CCCC1_0:P7P5g00YQR0g00Z1R:'81^75=60:dA]4H6C\b8b;b<X24X341176135@R@P@[[^24^34P7f8,2=#0f9#0P2f6O4b7b9b:b?b>b6131FePBPEE:9X=AE:W4W5W=X03o"). Qed.

(* [comment removed for export] *)
Lemma v_add_len_firstn : forall (p : word) n (bs : list byte),
  (n <= length bs)%nat ->
  v_add p (len_word (firstn n bs)) = p + nat_to_word n.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h01nh12b1h22b2h31zh41Hh52Hnh61bh72bsh81pp;1p;2p;3p;6p1006Kp4p70R0p100fAp4p710p8P0p100g7p4p710p8P0p100h1p4p710p8g00?Mj13Tg00@2j1:Tg00=Bj12Tg00F;j1<Tg00E[j2ETg00ZQj2@Tg00[oj16Tg00hkj28Tg00iaj34Tg00=ej31Tg00>?j20Tg00>ij3;Tg00jFj27Tg00@nj2DTg00jcj29Tg00BMj2CTg00kIj3?Tg005Pj65Tg00l7j2>Tg00Zkj3=Tg00Dcj2ATg00lfj3BTg00D>#3#3#3R0#3#3#3#:R1#2R2g00\j%:0#2R0#<f1R3f0R4,E0'@P2f2R5#6R6f4R7/84f3R8#6R99417R:512X62g00BgR;%24R<%23R=g00CE%25?134g00C`R>1085108331R?[1053105451>%28?153[R@%27?185\?A;534P4n2001000000120000000W2W1W0P@^2=^1<^0;P4P110171019'7R;,D1R<P:P>191;R=f5R@%67R?541,0191>4X3>P>P=101@101?'7,91=1>4X3>1C>=101:A?179E5101<1>1;E5O4b41886A4186512eA=053,A0AB534E5W5W7W0W8o"). Qed.

(* [comment removed for export] *)
Lemma v_add_len_firstn_Z : forall (p : word) n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  v_add p (len_word (firstn n bs)) = Z_to_bv 64 (bv_unsigned p + Z.of_nat n).
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h04Hlenh12Hnh22bsh31nh41ph51zp;1p;2p;3p;4p;6g00?Mj10Tg00@2j17Tg00=Bj16Tg00F;j1:Tg00E[j28Tg00ZQj2ATg00F[j12Tg00@Pj15Tg00G;j2<Tg00GXj2;Tg00>?j21Tg00jFj24Tg00@nj23Tg00=ej39Tg00BMj2CTg00Zkj3BTg00Dcj2@Tg00mij4?Tg005Pj6>Tg00hkj2=Tg00D>#0R0#0#0R1#0#0#0R2#7R3#6R4g00\j%71#6R1#:f1R5f0R6,81'A1815#2%50%52'<';g00C`R2f3R0#2R7f5,13R8/46,33f4R9#2,48,33594X521139/47,33R7,C4f2R29B10,@1R1,13P0P2P5P6C?E>1=91=947eW0W1W2W3W4o"). Qed.

(* [comment removed for export] *)
Lemma word_add_nat_Z : forall (p : word) (k : nat),
  (Z.of_nat k < 2^64)%Z ->
  p + nat_to_word k = Z_to_bv 64 (bv_unsigned p + Z.of_nat k).
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h01zh12Hah24__x1h32b1h42b2h51nh61Hh72Hkh87__arithh94__ffh:6__sat0h;6__sat1h<8__varmaph=5__with>4cstrh?1kh@1pp;1p;2p;3p;6p;4p;7p;8g00?Mj13Tg00@2j1^Tg00=Bj14Tg00F[j17Tg00@Pj1ATg00G;j2WTg00GXj21Tg00=ej36Tg00>?j20Tg00>ij3FTg00[oj1DTg00iaj3CTg00jFj29Tg00@nj2;Tg00jcj28Tg00BMj2?Tg00l7j2VTg005Pj6:Tg00H4j1UTg00HYj2TTg00IAj3MTg00Iej1LTg00F;j1KTg00JEj2JTg00Jcj1ITg00KAj1HTg00Klj2<Tg00LOj2GTg00M2j4=Tg00M]j1ETg00N?j3NTg00Nbj7OTg00OFj2PTg00Ohj2QTg00PTj3RTg00Q3j4STg00CER0j2BTg00Qej1]Tg00RNj3\Tg00kIj3[Tg00S:j2ZTg00SVj7YTg00T:j8XTg00C`R1f1R2f0R336p=2g00T^R4/Z3p=5P2g00U<R5g00U[R6P6g00V;R7P3g00V[FYp=@f3R8P5P6P6P7f2R9P2P3GXp=>g00D>R:#3R;#3#3#3#3#3R<#^R=#4g00\j%73%A;R;%A<R<'WR>'1g00BgR?%43R@%42RAP0%49?62310891082'2R0[10921093'2%48?692[RBf4RC#4?689\0AF923P3n2001000000120000000W4W3W5PB^4A^3@^5?P3P=%D9R?9C=8R@10=8RA%79RB'9R0,;=RDP110=?,9A,8=RA10=CRC%78'9RE,;=,0=RF,23X01P1PB19C3,8=/2FX01P118=0RF18=E/23X011?1F10=DRD1V=0E:1;=B,0=%U9%5BR01T;<114;%5<114>[[%5;RFg00W;REAM;<2UW1%5>\E^1Fg00WWRF#L%KF1J12%I1%H1RFP11<14g00XC1G1:R:C=,@FRE%E6R<PFP1P:g00Xj1<1;=N1=C=,@FR;P<PFP5P6P6P7PEP;FOC>C>1PF7P3P9g00YQRFg00Z1R7'?1Q39=6F7dAR142CSb9b<b=X21%53112>%59119>'B[[^21P3f6#7P8f5O3b8b:b;b>%]=,1B,B0e9\=BE:12ADe10=@A[=8?E:O4b6W7W?W@o"). Qed.

(* [comment removed for export] *)
Lemma v_sub_len_firstn : forall n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  v_sub (len_word bs) (len_word (firstn n bs)) = len_word (skipn n bs).
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h04__x1h14__x2h21nh31zh43Hn0h57__arithh64__ffh74__p1h86__sat2h98__varmaph:5__with;4__x3h<4cstrh=5cstr0h>1xh?2H1h@2HahA4__p2hB6__sat1hC6__sat3hD2b1hE2b2hF1yhG2z1hH1HhI4HlenhJ2HnhK2bshL1mp&0p;1p;2p;3p;<p;4p;6p;Bp;7p;8g00?Mj1?Tg00@2j1^Tg00=Bj19Tg00F;j1QTg00E[j27Tg00ZQR0j2\Tg00F[R1j10Tg00@Pj1VTg00G;j2gTg00GXR2j22Tg00=ej3>j1kTg00>?j25Tg00>ik304Tg00Dcj2BTg00Zkj3{Tg00njj2uTg00o`j3ZTg010>j23Tg010[j2qTg0112j2GTg011Oj1TTg00BMj2<Tg00c6l<PTg00S:R3j26Tg00]Ij4bTg00H4j1RTg011mj2aTg00CER4j2=Tg012Oj2LTg00HYj2`Tg00IAj3_Tg00^0j1JTg00^Oj2ETg012ik103Tg013Gk202Tg013hk301Tg00_8j3ATg00_aj2ITg00Iej1~Tg00`Mj3HTg00JEj2OTg00aKj4]Tg00Jcj1tTg00KAj1sTg014Qj1rTg00LOj2NTg0156j3STg00Klj2YTg00M]j1pTg00OFj2oTg00Ohj2lTg00PTj3mTg00Q3j4nTg015Yj4WTg016Dj3jTg005Pj6MTg00N?j3iTg00M2j4CTg00aij3UTg00mij4vTg00`mj1wTg016ej3xTg017alByTg018Gl<zTg018lj6eTg00SVj7|Tg00Nbj7}Tg019Pj7dTg00T:k800Tg00C`R5f1R6f0R73>p=1g00\jR8P8P8P5P5P5g01:4P1P1P1f6R9g01:Tf5R:f4R;f3R<f2R=P6P7MByp=hP8P5P5P5P1P1P:P;P<P=P6P7M<zp=fP8P5P0P1P3g00c[P:P;P<P=P6P7M<Pp=cg00T^R3/67p=:A>573p=KP6g00U<R1g00U[R0P0g00V;R>P7Eep=[P5P6g01;;P7CCp=@P6P1P0P0P>P7g00V[F|p=4P=P1P0P0P>P6P7F}p=FP5P6g00XCP7CCp=DP=P1P0P0P>P6P7Fdp=XP<P1P0P0P>P=P6P7L00p=8P5P;P<P=P6P7EMp=;g00D>R1#?R?#?#?R@#^#9RA#Q17A7,\617A6#0%V?RB%?@#?#?R@#VRC'gRD'2g00BgRE%97RF%96RGP4%9=?>6715<=15<6'1R4[15=615=7'1%9<?>=6[RH%9;?><=\4B04=67P7n2001000000120000000WEWDW2PH^EG^DF^2EP7%^@R@1BA<REA{A;<,BARF'uRGAZA;<RH,BAR415@ERI15@FRJ'3AZA:;,BA,5@RK,17X35%0;RL1BA;,5@RM/37/1KX3517A<RN#0RO%0:RP,37/1KX3517AHRK#0RQ17A;RR#0RS/3PRT/17X35P81qN;RU%07RV,1TX2813OLRT%0URW'11G3TRX,1TP5P5%k5RYP7X>5RZPY1167#TXF5X>5PTPT1<5TPWPXPZPZ1<5VX>8PUPX1367,G3XL5X25PNPO1<5ORTP;PL1<5LRYFhEfR[M<P1\;N16LOR\P;PLPYPNPOPTEcP=CbRTP\%RRRR%:SRS%R9RN%09#:RY17A9#0f7R]#0'3R^,a3R_123^1G3^R`/1^'=16^3%K`'='LR`17A]#0f8#0'3,G3R^P51`BCRa123B%:C123D[[Rb%:BRcg00W;RdA_BC6UW@RC%:D\d^@cRcp-0Rdg00WWReg00e6Rf#JRg#JRh#J,E5Ri&031-0251E5hRh60151E5fRf5A5Rj5A5g00eURk'I1E5g=A5f9A5hRh/Ik1Ijk%~eRj5He5He3H%QeRfP51O5=RgP61O5<C]Rl%t5Rm%s5Rn1[n:Ro%r1,N5Rp1N51R11N5?R?5S5Rq'@,4n5Fn1Y53Rr,Dq,4n1@pr,4n5Fn5Xn%p0R0Pn1D?1,4nP01@qp,4nC8C81on>R>P7P=g00YQRqg00Z1Rs'<1l7==>qsdAm536CnRsb6b9b:X05X15X;5W71376Rq,1=,=<16q3%K='='L16=613=</1;[[^05^15^;5^7dP7f;,7A#0Rqf<#0Rt'3Ru,23RvP<PtPqP;P]O6b5b8bCbGb?b=b<b4CWPKAjA;<RwEM15@4P8PU12VDX2812WD12XDP5P5P2PZP21267#TXF5X>5PWPXP[PDPD1<5DM<PPTP\PRPSPNPYP_P`P^P5PaPbPCPcAA5ih/Ik=HejPfPlPmPnAS5?p,@1,4n9Fno1[n91@1r,4n5Fn5XnP0Pn1Drp,4nP0PnP5P?g00XjRr1Y5B=i5@RBCC,4nP0P5P1PrPBCC,4nRBC8C8C8P>Psb6b9b:X05X15X;5X7dXAd136=,17,=<%K7,=;'L%:<12<DRrPr[[[^05^15^;5^7d^AdP716u3PvPtPqP<P;P:f9RqO8b5b8bCbGb?b=b<b4CWPKPwEMg00d=Rw,2Qe9UAHD;PIPTP\PRPSPNPYPaPbPCPcPjPf1O56PmPnPBP0PBC8P>Psb6b9b:X05127D126D[^05P717Aq#0RqP]O2b5bBb8b=b<b412Owe9UA<RAD;PJP;P<P=P6CvR<D;15@GPL167MX35PO16P7X35PTP\PRPSPNPYPaPbPCPcPjPfP5PgP6%w5C]PmPn1D1?,4nRnP0PnC8P>Psb6b9b:X05X151676166=[^05^15P7Pqf:#0P:O3b5bBb8b=b<b4PIPAD;PJP<D;9xEFD;O4bHWIWJWKX28o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "h02msh11Hh23ms'h32H0h42H1h52Hwh68IHmstepsh71kh84ms''h94restp;1p;3p;2p;7p1006Kp4p70p101;bp4p710p8g00?Mj10Tg00@2j14Tg00=Bj12Tg00F;j15Tg01<cj3>Tg01=Zj31Tg01>Sj1;Tg01?5j17Tg00M]j16Tg00=ej33Tg01@;j18Tg01ACj29Tg01B?j2:Tg01CGj7=Tg01D@j7<Tg01E9R0g00D>#0#0#0R1#4#2#5p-0\0p,4segsR2f3R3f2R43>R5P2f0R6f4R7;13f5R8=147[X20X00A1634P6W1X00%01#0#0#4#2R1#;%74%6133%8019231:0433f8R4f7R2513f9R1=184[A1714P2f6f:P1P7P3f1P6O1F=W5W6X45W3W1X80X20X00P7P3P6F<W1W7W9X20W0o"). Qed.

(* [comment removed for export] *)
Lemma to_wall_tail_nil_msteps : forall ms k,
  to_wall_tail ms [] k -> exists ms', msteps segs ms ms' /\ k ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h03ms'h15Hresth21kh32msh44resth53Hnbh62Hwh71Hh82Hkh94__p1h:2Hmh;4Hnb0h<5Hsteph=4Hsvch>2Hth?2IHh@7__arithhA4__ffhB8__varmaphC5__withD1ehE4ms''hF1xi001xp;1p;3p;2p;4p;7p;6p;8p;9p;<g00?Mj14Tg00@2j1?Tg00=Bj1<Tg00Iej19Tg01=Zj3@Tg00F;j1>Tg00BMj25Tg00=ej32Tg01<cj30Tg00CER0j21Tg01F@j2CTg01G7j4=Tg01GRj4ATg00^0j1YTg00E[j28Tg00ZQR1j26Tg01Glj37Tg00@Pj1VTg00S:R2j2UTg00]Ij4QTg00`mj1KTg00Jcj1JTg00KAj1ITg00Klj2;Tg00M2j4GTg00SVj7HTg00M]j1:Tg018lj6FTg00T:j8LTg00OFj2ETg00Ohj2DTg00PTj3MTg00Q3j4NTg005Pj8OTg01>Sj1PTg01?5j1BTg01@;j1RTg01ACj2STg01B?j2\Tg01Hej7[Tg01I\l9ZTg01J\R3j2XTg00c6l<WTg01E9R4f0R5'Xp=3g00\jg00C`R6P1g00F[P2g00c[f3R2f2R1f1R7g00e6R8g00T^R9P5M<Wp=Tp-0R:\4R;g00D>R<#4#4#4R=#?#<R>#9R?=@75P?%>>R@eRAP@15@5A2@5AA2@7?p,4segsRAf4RB;05RCP1P5O1'1X04#3]1X2;X4@X34P:^F4P5P7O1A2@??P4P2P5O1,1CX04P2A0A22P1P2O11CA2P7C=CAW1W8W2X34%Y8RC18>7'6A7217A2@2?P@P?18>5,6Cf7RDf5RE777f9RF=0A5PDP5O1'1X04RG#3]6]5X4@18>?,6Cf6R>?7?B16C8%V<R</U9R8PCP<156<1569CTP7CQP8g00WWRC#9%>C%K6%J6%I6RCg00U<RHg00U[RIPIg00V;RJPCPHPIPIPJP61;6<g00XC1;69CGg00V[FH%:IPCPHPIPIPJP1EFGL1ECJP5P1g00YQRJg00Z1RC'51D51=2JCdAM697CNbAbBbCX9:P7\8^9:P5f:R:=0A5f8R8P5O1R9'1X04#3P7O2b@b;W6W5PBP5P1P7GOW1W6W5X2;X4@X34%4=#4#4#?#<R=#P%B2%:=32%R41SAB1\4232A@B21A2@B?A0AD5PEP5O1'1X04#3]1A2@E?P7P5O1A0A85P>P5O1'1X04#3P3P4PGf;=0A5RG/19X04#3P5PFP5O1,1GP0f<R0=0A7P:P7O1f?R:=0A5P0P5O1'1X04#3P5f>RG=0A2f=RFPBO1P4fB=0A5P:P5O1'1X04PEfAR:=0AEPGPEO1PAP:f@PEPFP0P7F[P5C=CAW8W:P7P5O2n2001000000120000000W7XE4P7P5O2n2001000000120100000bDW1W?W>W<W=X2;X4@X04X34PBP7P2P1P5M9Zb1b4W7W2X34o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h01nh11Hh23Hbmh33Hssh41ki001kh52msi012msh64resti024resth75Hconth84Hevsh94Hfdch:2Hgh;2Hhh<5Hlazyh=3Hn1h>3Hn2h?3Hnbh@3HnohA2HrhB3HsthC4HsvchD2HwhE1ehF3evshG5modelhH2sthI2x8i032x8i041Pi051li061mi071xp;1p;3p;2p;4p;Dg00?Mj1<Tg00@2j1OTg00=Bj1ITg00F;j1ETg01>Sj1NTg01K6j1[Tg00M]j1ZTg00=ej32Tg01Kmj2XTg01LMj1VTg00Iej1STg01MEj3QTg01N:j1CTg01GlR0j3`Tg01O4j23Tg01Oij4DTg00^0j1KTg00ZQj25Tg00E[j2=Tg01P]j1YTg00Zkj30Tg00CER1j21Tg01?5j1WTg01QSj2GTg00>?j2UTg00@Pj1TTg01R5j2@Tg01S3j3RTg01T8lDPTg01G7j4?Tg01GRj4_Tg00Dcj2MTg01U9j2HTg01V9j1LTg01W6j1JTg00o`j3^Tg01=Zj3]Tg0079j4BTg01J\R2j2\Tf2R3f1R4f0R5'M'H#Lp=9g01WlR6%J5724p=:f4R7f3R8?^34;]5p=8f7R9f6R:f5R;P8g01XbR<P3P4CB727/15'1'1p=7g00\jR=/\5p=;1=45,53p=41M34,H8#L/35#J9267p=6P8P<P3P4CB92;7/15p=>1534/15p=FP3P<P4P5CB9278p=Ag01E9R>g00D>#<#<#<R?#O#IR@#ERAp-0\>RBg01YX%E<R<%<?#<#<R?#ORC#IRD#NRE%[3%ZD321XDDRF#E%V8%SF32p,2fdRFp,2chRG;Q7%C9f9RHf8RI;`9p,4segsRJf:RK/39P:P;CDP0PJf<R0,38f;RLPKCD%C8g00e6RM#KRN/55RO1=@;RP,55P<f>RQP@%YGRRA0@5;RSf=RTA9:@SRSf?RU'3':PSP@P5P;P7D8'1G7X0=#;]2]3P4%W81GD352Eg00C`1UC8%T?321@;M=2DF%NA1@:N%KN,@:5R:1GA73215NPA44@IA0@3H99L@P@P3PHPID8[\O^0=PJfLRP,3HfKRMfJR?CD%CIPJPFPGp,5Hfd32PLfNRGPKPHfMRFPPPMP?fIRJP9P:P;P7P5P8P4MDPPOA45@KP<PGP@PRA0@5KRKPFP0P@PKfORKD6G7X0=#;P2P=POA45@LP<PKP@PRA0@5LR2PGPTP@P2fPR2D6G7X0=POA45@0P<P2P@PRA0@50RGA9Q@GRGfQRC'3,:KPGP@P5P0PLD8'1G7X0=#;P5POA45@TP<PCP@PRA0@5TRGP2PUP@PGfRRGD6G7P115N41=@QP<PGP@PRA0@4QRQPCf@RCP@PQfSRQD6E>5F4POA45@CP<fTRGP@PRA0@5CR2fBRK?9@2R2fURE'3,:QP2P@P5PCPUD8'1G7X0=#;P515N8fARU,=@P<PEP@PRA0@7URUPGfCRGP@PUfVRUD6E>5F7P1A4;@KP<PUP@PRA0@;KRKPEfDREP@PKfWRKD6E>PO1=@ERU,55P<fXRCP@PRA0@5ER2fFRQ?9@2R2fYRS'3,:KP2P@P5PEPGD8'1G7X0=#;P5159UP<PSP@PRfE90@IRUPCfGRCP@PUfZRUD6E>P1P<PUP@PRA0@HQRQDAPSfHRSP@PQf[RQD6POA45@SP<f\RUP@PRA0@5SR1A9?@1R1f]RE'3,:QP1P@P5PSPCD8'1G7X0=#;P5P<PUP@PRA0@LSDAPUPMP@A0@0Jf^R0D6P=POA45@MP<f_ROP@PRA0@5MRUA9F@URUf`'3,:0PUP@P5PMP?D8'1G7X0=PT15NTA4T@?RNP<P0P@PRA0@T?RRDAR0A9P@RRR/3O,:EREPRP@PTP?PJD8RJ'1R?'1R@'1PHPNP@P;P0P?P4PEPJP5PGPTPHP;O3C?C?C?C?C_WBW8P4P5O2n2001000000121000000W1W>P4P5O2n2001000000121000000W1W=P4P5O2n2001000000121000000W1X0=P4P5O2n2001000000121107000bEW2W3W7W?WAW:W@WCX4BX6AXIDX5>PHPIP9P:P;P7P8P3P4P5O:n041061051040000001:1101103102100000000000000000000P5P3O2W3WDW2W9W<W;XH6WFWGW4W6W5o"). Qed.

Lemma to_wall_no_error_sstep : forall ms rest k model evs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  buf_modeled rest ->
  to_wall ms rest k ->
  ~ sstep segs (mkCfg ms model) evs SError.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h01Hh11nh21eh33Hbmh44Hfdch52Hhh65Hlazyh73Hssh83Hsth92Hwh:2_Hh;3_H0h<3_H1h=3_H2h>3evsh?1kh@5modelhA2mshB4resti001ci011si021xp;1p;3p;2p;4p;<p;6g00?Mj19Tg00@2j1ATg00=Bj1?Tg00F;j1=Tg01>Sj1XTg01K6j1UTg00M]j1JTg00=ej3;Tg01Kmj2HTg01LMj1FTg00Iej1ETg01MEj3CTg01N:j1BTg01Glj3WTg01O4j26Tg01Oij4VTg01ZNl<TTg00^0j1QTg00ZQj23Tg00E[j27Tg01P]j1ITg00Zkj30Tg01J\R0j2GTg0049j6KTg01[Oj2DTg01[nj1LTg0079j4MTg00Dcj2NTg01U9j2OTg01V9j1PTg01W6j1@Tg00o`j3RTg01=Zj3STg00CER1j2>Tf4R2f3R3f2R4g01XbR5f1R6f0R7CM3;p=51N67,O4#Pp=1g01WlR8g01\GR9%@73;p=8AR346=S27p=21>67,>4p=41667#@p=:A;896/>7p=<g01E9R:g00D>#9#9#9R;#A#?R<#=p-0R=\:g01YX%=5R5%9;#9#9#A#?R;#X%U6%J;3;1H;;R;#=%F4%E;3;p,2fdp,2chR;;C3f6R:#Bf8R>f7R?;W:p,4segsf9R@/6:f5RAP9CVRBf:RCP@P>P?P:P9PAP2P3P4P6P7M<Tg00\jR4g00e6#QR:/37RD17<C,37P5P?P<%I;R;A0<7CRED5f;RF?1<ERE/6>#8PEP<P7PCP@D23434X14'GP0P417<F,37P5P>P<P;A0<7FR0D5f<RE?1<0R0/6@#8P0P<P7PFPCD23454DX14g01]=R0P7f=RG,7<,37P5PCP<P;A0<7GRCD5f>RH?1<CRC/6F#8PCP<P7PGPED23454DP113:617<H,36P5PFP<P;A0<6HRDD5f?RC?1<DRD/:EPDP<P6PHPGD2'<34P0P713:3fAR:,7<,32P5PHP<P;A0<2:RHD5fBR3?1<HRH/:CPHP<P2P:f@R2D2'<34P117<3,3AP5PCP<P;A0<A3RHD5fCRD?1<HRH/62#8PHP<PAP3P:D234P0P7fDRA,7<,3?P5P3P<P;fER390<>R?D5fFRH?1<?R?/6D#8P?P<P>P3PAD234P1P5PDP<P;A0<@HRDD5fGR>?1<DRD/:APDP<P@PHP3D2'<P0P7P5P3P<P;fHR;90<FD5fJRFfIR390<E71<R5/:>P5P<PEP3P;D2'<P1fKA0<GF71<R1/6;#8P1P<PGPFP3D2P0P7fMR3fLRG90<C71</6F#8fNRFA0<2371<P<P2P3PGD2P8P9P8P=P7P0g00W;n0110100021010000X28g01]ZfOA0<:F71</:GP6EKP01D07b0W=W8P6P7O2n2001000000120000000W0W<P6P7O2n2001000000121000000W0W;P6P7O2n2001000000121000000W0W:P6P7O2n2001000000121000000W0X14P6P7O2n2001000000121102000b2W7%LBeW9W3W4W6W5W>W@W?WBWAo"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h01ch13ms'i003ms'h21kh32msh43Hbmh52Hkh61lh74resth82IHh91mh:1Hh;5Hconth<3Hnbh=5Hstarh>4Hsvch?1eh@1nhA4HfdchB2HghC2HhhD5HlazyhE3HnohF2HrhG5HstephH2HthI2HwhJ5modelhK1ohL4tr_khM1xi011xhN2x8p;1p;3p;2p;4p;6p;@p;=p;8g00F;j1MTg00?Mj1>Tg00@2j1XTg00=Bj1RTg01>Sj1NTg01K6j1qTg00M]j1dTg00=ej31Tg01Kmj2ETg01LMj1\Tg00Iej1<Tg01MEj3[Tg01N:j1:Tg01O4j24Tg01P]j1pTg01?5j1cTg01QSj2ITg00>?j2bTg00@Pj1aTg01R5j2GTg00^0j1QTg01S3j3]Tg00E[j22Tg00ZQj2CTg00Zkj37Tg00Dcj2=Tg01U9j2BTg01V9j18Tg00o`j35Tg01=Zj3PTg01^6j1OTg01^Zj3ZTg01_Zj4@Tg00BMj2JTg01`Mj2yTg005Pj6DTg01`kj2xTg01aJj4YTg00`Mj3wTg01ajj6vTg01bhj2uTg01ccj2tTg01W6j1oTg01Oij4nTg01d\l@kTg01eXj1jTg01f^j2iTg01ggj3hTg01i8l=fTg01ilj3eTg0049j6KTg01k8j8TTg01GRj4VTg01Glj3gTg01@;R0j1STg01ACj2WTg01B?j2ATg01kkj1lTg01m3j1mTg01n;j3`Tg01o7j4_Tg020;j8rTg020oj6^Tg01J\R1j2sTg0079j4LTg009hj3FTf4R2f3R3f2R4'4f1R5f0R6C@p=6g021mR7/s6p=0P4g01XbR8P5P6CLp=?P2P3AF845P6C@p=Uf7R9f6R:f5R;'4P2P8P3P4CL=F85P6C@p=3P3P8P4P5CL=F86p=;AF856p=9g01E9R<g01YXR=P5P6CYp=H%M8R>g00D>#>#>#>R?#>#>#>R@#XRA#RRB#NRC%q5%dBRD311EBBRE#M%\4%<ERE31p,2fdRFp,2chRG;[3%X?#RR?#MRHp-0RI\<RJ%:5P4P6O1p,4segsRKP4f;RLf:RMP6D6X07#0RN[^1<PK14;MRO%pGRP=??2f9RQP6DUX07#0[[W2W7X3<RRPR%c3RR1IB451Cg00C`1bA3%a@31g00e6R@,G;=1BF%NH%Q@R@,G:%Q@,G:5]:1IH23112?;,C@g00\jRA1C@6RSf8RT,2?,C5A7?4Q,=?,BL#8A5?4Q;PT[[]@12?Q,C5A5?4M#:PLP6O1PKP4fERUfDRVP6D6X07#0[^1<PKf?RWf=RX97?;,=?'B#8PVP?PPA5?;XfCRYP6G3X07#0[[[\S^@A%:TPQP6O1PKP4PYfBRSP6D6X07#0[^1<P412?MRZP2%OZAZZM5P6O5PK12?LRZ=7?L,=?,BX#8PSP?PPA5?ZLfARZP6G3X07#0P1P7PKf>R[f<R\,2?R]=7?\,=?'B#8PYP?PPA5?]\PSP6G3X07PK14WVR]P?PPPXPYC;R^P6C@X07R_#0P6PKf@R`12?[Ra=7?[,=?'B#8PUP?PPA5?a[PVP6G3P7PKfGRa,4SRbA??P`RcfFRd'9ReP6C@X07P5PHPWA??P6RfP?PP12?`Rg=5?`PdC;Rh'9=1>eX6HPH%<?Ri19fd,9c=1>eX6HP?PPPWPUC;Rc,J>12?WRf=5?WRj1y?WEDA7?fWRf1x?WEDP?PPPfP?PPPjPUC;C;=1>cP>A7?g`Rc9??PRj/9hPKfHRf,4YRkP6P3C@X6>PKPbPj1=?cRc,BSRb#8/4aPhP4P<1EBARhPBPA1GS@PgCY%<hRh3wRAPc1EBH#<PEPEg022b#<PhEv'uRh,tSPKPk12?Z=7?Z9??P%86/4f#oCnX9<PKPSPaPZPhPaPaPjPUP[PKPSPZPaPFPGP`PgPYp,5Hfd32PXP\PLP9PM%OgM@kPU%N=Rg1I=aRY1I=f91g6XKg1JgY%jhRh,iaAhahVEDM=fPbAeScAEKP5GTPeP6EKb:CVW=X07P5P6O2n2001000000121101000b?W5W4W8W;W<WFWBWEW>X2JX7HXNBX3<PI^M<P6P5O1%:iP3P6O1PN[^1<P6P2P4O2PKPOA??PiPQP6DUX07#0eW;W4W5W2X3<12?5,C@Ag345%:3P2P6O1PKP4PXP\P6D6X07#0[^1<PKP9P\P?PPP:PLP6G3X07#0[[%:2R@P;P6O1RiPKP4P[PXP6D6X07#0[^1<P4P5P6O2ROW5W4W8WIW<X2JX7HX3<A1CRD%S<RR1WK21A<331AP234PKP4PWP[P6D6X07#0\i^1<PKPTP[P?PPP9PXP6G3X07#0[\@%:;P:P6O1PKP4P`PWP6D6X07#0[^1<POPKPQPWP?PPPTP[P6G3X07#0P1P7PKPMP`P?PPPQPWP6G3X07PKP\PZP?PPPMP`P6G3X07#0P6PKP\PSP?PPPLPZP6G3P7P_P5P?PPP\PSC;R\,J>%<8R8P>e/9\=1>\P>198^PKP`PUP6P3D6X6>PKP]P814[VP^P4PKPWPVP[PVPSPL1E<=RL#SRSP0P<PS1WKWR41H6U,AL%lLR8%mLR]n10110100031010000001HWU,ALRU91S6X9SPR1A<[P0P<PSP61H6d,ALP8P]n1011010003101000000=1SUX9R1H[V,AL,JSP4PMEDA`KWVPKPWPVPZC_EDGrP5GTP^P6EKb:CVW=X07P5P6O2n2001000000121101000b?W5W4W8WHWGW>X2JX7HX1<X3<E^WAWDWCWLXJ=o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "h01ch11kh22msh34resth43ms'h53Hbmh64Hfdch72Hhh82Hkh95Hlazyh:2Hwh;5modelh<4tr_kp;1p;3p;2p;4p;5p;9g00?Mj10Tg00@2j17Tg00=Bj16Tg00F;j11Tg01Glj3FTg01N:j1DTg01>Sj1>Tg01K6j1=Tg00M]j1;Tg00=ej35Tg01Kmj28Tg01LMj19Tg00Iej1:Tg01MEj3ETg01O4j24Tg01_Zj43Tg01J\j22Tg01P]j1CTg0079j4BTg009hj3?Tg01=Zj3@Tg023Zj5ATg024al9<Tg01E9R0g00D>#0#0#0R1#7#6R2#1R3p-0\0R4f2R5f1R6f0R73FR8%D5R9g01YXg01XbR:#1%01#0#0#7#6R1#>%=6%;1351811R1#1%95%:135p,2fdp,2chR1f3R;3Ef8R<P7O1g021mR=p,4segsR>f7R?,45f6R@P7C3X0='2[^40P;P7O1P>f=,45f<RAP7C3X0=,2=[^40P>14@AP2P:%C1f5R1CBf;5?:P7C3X0=,2=[\9R9\8^14^33^20A@567P9[^14^33^20P1f4P;P5P6DAf:f9P<P?P@P7M9<W8W6W9W7W<W;W5W:W1W3W2o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "h01ch11kh22msh34resth43ms'h53Hbmh64Hfdch72Hhh82Hkh95Hlazyh:2Hwh;5modelh<4tr_kp;1p;3p;2p;4p;5p;9g00?Mj10Tg00@2j17Tg00=Bj16Tg00F;j11Tg01=Zj3FTg01N:j1DTg01>Sj1>Tg01K6j1=Tg00M]j1;Tg00=ej35Tg01Kmj28Tg01LMj19Tg00Iej1:Tg01MEj3ETg01O4j24Tg01_Zj43Tg01J\j22Tg01Glj3CTg01P]j1BTg0079j4?Tg009hj3@Tg023Zj5ATg025<l9<Tg01E9R0g00D>#0#0#0R1#7#6R2#1R3p-0\0R4f2R5f1R6f0R73FR8%D5R9g01YXg01XbR:#1%01#0#0#7#6R1#>%=6%;1351811R1#1%95%:135p,2fdp,2chR1f3R;3Ef8R<P7O1g021mR=p,4segsR>f7R?,45f6R@P7C3X0='2[^40AC567P;P7O1P>f=,45f<RAP7C3X0=,2=[^40P>14@AP2P:%B1f5R1C?f;5@:P7C3X0=,2=[\9R9[^14^33^20P9\8^14^33^20P1f4P;P5P6DAf:f9P<P?P@P7M9<W8W6W9W7W<W;W5W:W1W3W2o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h01ci001ch12H1h22H0h35Hstarh42tri012trh51Hh63Hssh76Hstar2h81li021lh93ms'h:3Hc2h;1kh<2msh=1nh>2H2h?2HKh@3HbmhA2c2i032c2hB3evsi043evshC4resthD2IHhE1ehF4HevshG3HnbhH4HsvchI2c0i052c0hJ2c1i062c1hK2c3i072c3hL1si081shM3tr2hN5HconthO4HfdchP2HghQ2HhhR2HkhS5HlazyhT3Hn1hU3Hn2hV3HnohW2HphX2HrhY5HstephZ2Hth[2Hwh\1Th]1ah^2l2h_5lemmah`5modelha1xi091xhb2x8p%0p&0p;1p;3p;2p;4p;7p;6p;Dp;;p;:p;5p;9p;8g00F;j1`Tg00?Mj1LTg00@2j1jTg00=Bj1bTg01>Sj1nTg01K6k10FTg00M]k10CTg00=eS00j32j1]Tg01Kmj2|Tg01LMj1vTg00Iej1ZTg01MEj3oTg01N:j1ETg01P]k10GTg01?5k10DTg01QSj2lTg00>?k20BTg00@Pk10@Tg01R5j2\Tg00^0j1iTg01S3k308Tg00ZQj2VTg00o`j3JTg01=Zj3cTg01O4j20Tg01_ZS01j48Tg00g7j2aTg0049j7Gj6FTg01W6j11Tg01Oij4NTg01T8mD0HTg00Zkj35Tg01J\R0k20ETg0053j6kTg00Dcj2RTg01^Zk30ATg009hj3@k107Tg001?k40?Tg025Wj4PTg00fAk10>j3OTg026>k30=Tg026oj4TTg027fj3[Tg028\k40:l:}Tg029Ij2hTg02:5k109Tg007Uk306Tg0079k205j4QTg00:bk204Tg02:dk103Tg0094k401Tg02;Uj3{Tg02<Mj4zTg02=@j1yTg02=oj6xTg02>Zl;fTg02?Uj3wTg01;bk500Tg02@6j4uTg02@Tk502Tg005Pj6dl9ej8gTg00BMj2KTg01Glj3tTg01@;k10;Tg01ACk20<Tg01B?j2sTg02A0l:rTg020oj6qTg00E[j2pTg01U9j2^Tg01V9j1_Tg00CES02j2YTf4R1f3R2f2R3'0f1R4f0R5C8p=4g01XbR6?O45p=7P2P6P3P4CQ=@659O61p=61p45,V3p=;A5345,R2p=H1^45#_p=Bg021mR7?245p=3P2P6P3P4CQ=@65p=?10459273p=DP7P1P2P3P4P5Edp=CA@645p=9P11023P4P5CNp=AP3P6P4P5CQp=:g01WlR81R34,^2#_/05#1721p==A2234/Y5p=M1Y45,Y3p=SP3P6P4P5CQ9212p=XA@634=O65p=Uf5R9=@61P2P6P3P4CQ=@655O6p=<1R34,^2#_/05p=mA2845p=>1045#1p=IA@6459O63p=~%159284p=Wg01YX%`6R:g00D>#L#L#LR;#L#L#LR<#jR=#bR>#nS03&0F4&0C>S04321|>>R?#`%v3%Z?32p,2fdR?p,2chR@;o2g01E9RA%j;#bR;#`RBp-0RC\ARD%E4P1P3O1p,4segsREP2f<RFP3P4D4172F[S05[^07^4:^9APEf6RGf;RHP4P5D4S06P3P;&0G@RIPGPHD6[^07^4:[[W;WCW<RJPJQ03&0D2S071l>332g00C`20B=2&0@<32g00e6R<,\9=2>?%nB%i<R<,\G%i<,\G608G1lB132A;<;9g00\jR=1V<5RJf8RK9;4;P;P;P3f9RLCH,BHAJ;3L;cK[[]=A;4;Lf:RM9J;3#Ef=RNP3O1PEP2fFROP3P4D4172O[[^07^4:^9APEf@RPP;P;PGf>RQCH'BfERRP4P5D4P3P;PIf7RSf?RT5J;PRD6[^07^4:[[[\J^==%EKPHP3O1PEP2fDRUP3P4D4172U[[^07^4:^9APEfCRV,0QS08P4P5C8Q01PEfHRW,0VS09,32A2:2SS0:132SS0;P;PIPUfJRXC?S0<,7L[[[P5fARY/0OS0=,35%Z6RZ=2:9S0>1339S0?fIR[9D2UP510RXS0@,31fKR\,0OS0AA2:ZMS0B134MS0CP;PIfGR]fMR^C?S0D,7F]1]2X07A2:ZLS0EP5Q0BP:PZfNR_,0[S0F/3HR`P;PIPWP_C?S0G,74]1X8:10W^S0H/3MP5P`P7fOS0I,0XS0JPZP;PIP[Q0ID6X07P:PZPEfPR`,0\RaP5PNC8P;PIPXP`C?Rb,7Z]3X4:PEQ0JPZPFC8P7PaPEfLRcfQRdPZP5D4PZP;PIP\PdD6]3X07PEPaPZPaC81a6bW3PNP3P5FGW3PNP2PHFGPFP5EFb>W1PHP5EFb1W2P9P5DCb2W5P3P4P5O3W1W2W5XI7P5O1PEP1P2%13S0KCNS0LPEP2P3P4C8S0MfRRb,0^S0N,3G19G1=2:YS0O131YS0PfURa9DL`P5fVRe9DMdfWRf,0b19HL=2:OS0Q13LORgPEP3PN%1FCNS0RPEPNPFPHC8S0SP;PIPaf[RhC?S0T,7X]7]6]1]2X0719MK=2:RS0UP5Q0QP:19FMS0V13M]S0WPE10ehS0XPQ%1NS0YCNS0ZPEPQPNPFC8S0[P;PIPef\RiC?S0\,72]7]6]1X8:P5Q0WPWPEPfPiPT%1QS0]DAPEPTPQP4C8S0^19YTS0_P;PIPff]RjD6]7]6X07Q0ZPEPQPNP[C8S0`P:19PQS0aPEfYRkf^RlP5P\D4fBRm/9PS0bP;PIfXRnPlD6]3X4:PEPnPjQ0aPXD4PEP?P@p,5Hfd32PkPlPnPfPY%1PS0cPiPhfZR@PafTR?fSRoPbP_PdP3ND0HA;5;nP:PmA5;5nRp9:;I%1YS0dP@P;Ppf_RpD=CM5SJX==-0E=P0P=A;5;kP:PVA5;5kR09:;I%1mPhP;P0f`R0D=CM5SJX==19VYS0eP;PIPkPpD6P5A;5;hP:PRA5;5hRq9:;I%1US0fPjP;PqfbRqD=CM5SJQ021V<4A;4;iP:POP;PIA5;4iRJDX%1RPlP;PJfcRJD=3SP;PIPjPJC?S0g9U]RP51V<2A;1;pP:P[P;PIA5;1pRrDX%1WS0hfaS0iP;PrffRrD=3SQ02A;9;0P:PXA5;90Rs9:;I%1[S0jPqP;PsfgRsD=CMP;PIQ0iPsC?S0k9U\[P5A;S;qP:P^A5;KJRt9:;I%1cfeS0lP;PtfjRtD=CMQ02P:P_P;PIfdRu95;LRvDX%1^PrP;PvfkRvD=Q0IP^P;PIQ0lPvE<P5P:P`P;PIA5;HrDX%1`fiRwP;A5;FsfnS0mD=P:fhS0n95;N9:;IRxPEfpRy,0vRz195dPjC8PEflS0ofqR{P4%1oR|DAP3PoP;PIPvP{E<]6]3XB:PEPtfoR}19x`PiD4PEPzA5;Qw9:;I%1bCNQ00P8P|Q0mP;Q0o95;YS0pfsRzCmS0q#1S0r,>4fmRx95;mR~9:;IPaP;PIPxPzE<[P3Q0oP;P;PTPtCH'B/I{S0s,>|%1?P;P;PPPvCH,BxfrRx'IS0t'>P8P7P8P7P5P5Pen0110800021010000XE8%1aQ0rP5EkQ0q,3a1R;~,B}ftR~5DeP5P;P;PVQ0mCH,Byfu5DfP{P;A5;U}S0mfvR}CmRfA5;RyRv9:;IR|PnP;PIPyP}E<X07P7PfPEPxfwS0qP|%15S0rDAPEP4PkQ0lC8Q0KP~P;A5;]xfyR|D=A5;WzS0u9:;IRyPhP;PIPzP|E<]:]7]6XA7PEP{P}Q0m9:;I%1fDAPE1R;v,BxQ0qPnPuD4P;P;POP{CH,BzfxR{'IRv/>vPtP]PVPTB0A]xwQ0nP@PrP4O8P@P;PIAJ;]xP{D6Q0uAJ;WzS0q5@;S0m=2BzP:PC^^:R{%]:RvP:PCPvPCPCPCg02AoS0vH0?S0wCPRf&0>6S0xP{\:S0yP:P{PvPfCPR}Q0yP:P{PfP:PCQ0wQ0vg02BM60=CCTCT7[}Q0xH0:P;PIA5;[~R}PiC?Rf1h:fA:;I~S0xfzR{'9AJ;[~9@;}S0y9:;IS0v/9{P:\:S0w\:S0zP:Q0wPvP:P:PvPvCPS0{CPR}Q0zP:Q0wQ0{P:P:Pv&09:CTCT7[}&076Q0xQ0vP6\;S0vP:^8B%]6S0x:06;6R}PBP:%]BS0zPvCP205;6204;6PIQ0vP}Q0vQ0vP;P6Q0x&036H017{}7[}PICzP~Q0yPBQ0z%yBQ0yP~P5ExM;fP{P{1h:{M:}M;fW_Aw;WzP:Q0q9:;IRz,9yR~A~f5{X8:P:19z|R{,9y17f5X8:P6PyPhP{P5I0019~|P6PyPzP|CuEFQ0m9:;IP;P6PIQ0uQ0qI02EdO2bWW:W7W6PnP4P9P[PSM9ePnP5DCb1W2P5O1b2W5P5O1W5n2002108000000101Q0t,>5Q0p9:;IP?P;PIQ0oPxE<[XL8Q0sO1P5Q0t,K8O1b5W6W3PbP4PYPVGgW:WFP4P5O2n2001000000121000000W5WUP4P5O2n2001000000121000000W5WTP4P5O2n2001000000121000000W5X==P4P5O2n2001000000121109000bEW3P\P9P[FGW7W6PHP5DCb>X1gP]P5EFb1W2PHP5DCb2W5P3P4P5P1P2O5W1W2W5W7W6XK7XM:XA7XB:XJ7PGP9P1P2P3P4P5O7n1041001021050000002111007110610410310110700000010m]R=,33A2:3GRx133GR|PKP;PIPVP[D6[[[X07X8:X0710TURVP3P4O3P510PRRz,K71K:2Ry1K73R~O3b5W3X07X4:W?W@WDWNWGWXWPWVWHX;DXCBXb>X<APC^aAP5P4O1%Z;RC#EP9P3O1Q05[^07^4:^9AQ06P2PSP3P4P9P5O5P3P;PIPCPHD6eW3X07X4:W?W@WRW;X<AA;<;4At234%E2PGP3O1PEP2PQP3P4D4172Q[[^07^4:^9APEPKPNP4P5D4P3P;PIPKPND6[^07^4:[[%E1R<PSP3O1RCPEP2PTP3P4D4172T[[^07^4:^9APEPLPQP4P5D4P9P1P2P3P4P5O5W3X07X4:W?W@WDW[WGX;DXCBX<AQ03Q07Q0432&0;A20<E11sA232Ac123PEP2PPP3P4D4172P[\C^07^4:^9APEPLPTP4P5D4P3P;PIPLPTD6[^07^4:[\<%E9PKP3O1PEP2PYP3P4D4172Y[[^07^4:^9APEPHPPP4P5D4Q01PE132zQ0:Q0;PLP;PIPYP]D6[[[P5Q08,35Q0>Q0?Q0=,32P5131=Q09Q0BQ0CQ0<,7F]1]2X07Q0EP5Q0BP:PZQ0A/3HR=P4P;PIPRP\D6]1X8:Q0@/3MP5P=P710]cR=PZP;PIPOPcD6X07P:PZPEQ0HP5PNC8Q0D,7Z]3X4:PEP=PZPFC8P7Q0HPEQ0FPZP5C8Q0G,7Z]3X07PEQ0HPZQ0HC8Q0D,a6W3PNP3P5FGW3PNP2PHFGPFP5EFb>W1PHP5EFb1W2P9P5DCb2W5P3P4P5O3W1W2W5XI7P5O1Q0LQ0MQ0J,3GQ0OQ0PQ0N,3LP5ADM_oQ0I/0?Q0QQ0RQ0SPXP;PIPbPnD6]7]6^1g]2X07Q0UP5Q0QP:Q0VQ0WPEPoPnPQQ0YDARQQ0[P2P;PIPoPkD6]7]6]1X8:P5Q0WPWPEP?PkPTQ0]DAQ0^Q0_P;PIP?P@D6]7]6X07Q0`P:Q0aPEQ0XP5P\C8Q0bQ0T'7]3X4:PEPaP@Q0aPXD4PEPePhPaPYQ0cPnPbPdP3M:rP:PYPZQ0c10ah'WCMQ02A2:mZQ0d10ei'WQ0eQ0\'7P5A2:UZQ0f10kp'WP:PZPEQ0i,0iRe195RPdC8PEPjPqP4%1]RdDAP3P]P;PIPiPqE<]6]3XB:PEPhP019ZUP`D4PEPePZ%1OCNQ00P8Pd10luRe#1R`,>4PZP[P;PIPlPuE<[P31IiqRU,>dQ0h1IjJRd'>P8P7P8P7P5P5PXn0110800021010000XE8Q0jP`P5Ek13[eQ0l9DXpP5AD\0rQ0i/0sRrQ0k9UZcX07P7PrPEPJQ0nPZQ0rDAPEP4P^PkC8Q0K10ut'WPZQ0IP;PIPuPtE<]:]7]6XA7PEPqPsPZ%1rDAPEPqQ0nPcPnD41IJwRn/>nPlPjPiP_P@P4O5PZP_P;PIPJPwE<eW:W7W6PcP4P9PNPSM9ePcP5DCb1W2P5O1b2W5P5O1W5n20021080000001001>5dQ0g9UZW[XL8PUO1P51K8dO1b5W6W3POP4P9PSGgW:WFP4P5O2n2001000000121000000b]W3P\P9P[FGW7X6QPHP5DCb>X1gP]P5EFb1W2PHP5DCb2W5P3P4P5P1P2O5W1W2W5W7W6XK7XM:XA7XB:XJ7PGP9P1P2P3P4P5O7n10410010210500000021110071106104103101107000000133VPKP;PIPPPOD6\|\x[X07X8:X0710FYP3P4O3P510Nm,K7PyP~O3b5W3X07X4:W?W@WDWZWYWHX;DXCBX9AX<AEqWOWSWQW\W`o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "h01ch12trh21kh32msh44resth53ms'h62HKh73Hbmh84Hfdch92Hhh:5Hlazyh;5Hstarh<2Hwh=1Th>5modelp;1p;3p;2p;4p;5p;<g00?Mj10Tg00@2j17Tg00=Bj16Tg00F;j13Tg01Glj3FTg01N:j1DTg01>Sj1>Tg01K6j1=Tg00M]j1;Tg00=ej35Tg01Kmj28Tg01LMj19Tg00Iej1:Tg01MEj3ETg01O4j22Tg01_Zj41Tg00fAj34Tg01P]j1CTg0079j4BTg009hj3?Tg01=Zj3@Tg02C>j5ATg024al<<Tg01E9R0g00D>#0#0#0R1#7#6R2#3R3p-0\0R4f2R5f1R6f0R73FR8%D5R9g01YXg01XbR:#3R;%01#0#0#7#6R1#>%=6%;1351811R1#3%95%:135p,2fdp,2chR1f3R<3Eg021mR=f:R>P5O1p,4segsR?f8R@,2<P5P6C1A4:<@[[]0^1;^50P?f<RAf7RB'2P6P7C1f5RCP5O1P?fARD,2<P5P6C1A4:<D[[^0=^1;^50P?f@R?,2BP6P7C1P2P:%C1PBCB=?:?94:5[^0=^1;[\9R9\8^24^43^30A@567P9[^24^43^30P@PBf6PCf4DAf=PAf;P>f9P<P5P6P7M<<W;X0=X1;W6W8W:W9W=W>W7W<W2W4W3o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "h01nh11Hh21bh32b1h42b2h53E10h63E11h73E12h83H10h93H17h:5Hconth;3Hn1h<3Hn2h=3Hnbh>2Hrh?1kh@1mhA3memhB2pchC4regshD4resthE3romp;1p;2p;3p;8p;5p;6p;7p;:g00?Mj12Tg00@2j1FTg00=Bj13Tg00F;j1QTg014Qj1?Tg00;Aj2VTg01>Sj1DTg00@Pj17Tg02DCj2;Tg02Dfj35Tg02EIj29Tg00>?j24Tg00=ej30Tg02F>j21Tg02Fhj1WTg01QSj26Tg00M]j1UTg02G`j1TTg02HWj8>Tg01S3j38Tg00^0j1NTg00E[j2CTg00ZQj2<Tg00Zkj3MTg00Dcj2LTg02I^j3KTg02JUj2JTg02KLj5HTg00o`j3GTg01=Zj3ITg00>ij3RTg00F[j1BTg00jFj2ATg00@nj2@Tg00BMj2:Tg01?5j1PTg005Pj6=Tg02LAj1OTg01R5j2ETg01U9j2STg01V9j1ZTg02M@j7YTg02N7l:XTg01E9R0p-0[g00D>R1#2R2#2R3#2R4#F#3R5#QR6%?2R2#FR7%24#2#2R8#FR9#3R:'V%D5\:R;g00C`R<f3R=%?4#7R4g01]ZR>1;74d557R?'9,49%7830f4R8%22#7R9P>1;79d557R@'1p,2fdRA50:%D6RBf5RCp,2fxRD#WREP819C?,6:%U:R?%TDRFP=f2RGG>%?2#7R2P>1;72d557RH,1C%?1#2#2#7R1P>1;71d557RI,1C38f6RJ,6630g00e6RK#NRLf7RM,C5'<g00\jRNf0RO,<LRPf1RQf:RR,C5'<PDf;RS9M5G,L59KR@f9RT%73R3'Jf8RUPMDHAG5GSf<RV3I[[]0g00BgRW%3ORX%3QRYg00CE%3G?0QO14=G14=Q50<RZ[14GQ14GO50<%3=?0GQ[R[%38?0=G\ZARGQOPOn2001000000120000000W4W3W0RZP[^4Y^3X^0WRWPOP7%BK,A9,@7RXA579>RY147Y,:<O4b1%37R[P@P[e70XPZPWPOP7%BL,A9,@7R@A572>R21472,:<O4b1PHP[e90[@PZPWPOP7%NLRW#B,A9,@7R9A571>R11471,:<O4b1PIP[e90[9PSPEPRA574>R>,9SR4,6:R7P?PFPTPUG>RUP4PVf=R4%D:RI/:7%PU=0I7ePMP[PY11VORM=0:AX2[PJPXPGE=%OURI/1X=0:Ae1EUK=0:AeP[P2PVPEPS19V>,6:P?PFPRPTG>RT11V978M1664RR50BX2[P[P111V2=8TM=0BRX2[PCP9POE=P@PQE=11I@11I958U166VR650Be1EUL1EUW58U=0B6eP8f>R8,C5,<QP0PDf?9M5G,L5R69K8Y1J43PVPSDHf@9G5=fA5IOX@0PJPGPQPOO3P8PEP4198>,6:R>P?PFPVPSG>/S6#ZPDP8P4P>PVPSP6FYE=W<X;PX0NM:Xb7b6b5W:W=W>W8W9XE;WAXB:WCWDW?o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "h03ms'h11kh22msh34resth42IHh53Hnbh64Hsvch71nh85Hconth92Hgh:2Hkh;3Hnoh<2Hrh=5Hsteph>2Hth?2Hwh@1xhA2x8p;1p;2p;3p;4p;6g00?Mj11Tg00@2j1;Tg00=Bj17Tg00F;j1=Tg01J\j24Tg01>Sj19Tg01?5j1DTg01QSj28Tg00=ej30Tg00>?j2>Tg00@Pj1<Tg01R5j25Tg00^0j16Tg01S3j3MTg00E[j23Tg00ZQj22Tg00Zkj3LTg00Dcj2KTg01U9j2JTg01V9j1CTg00o`j3BTg01=Zj3:Tg01^6j1ATg01GRj4@Tg01Glj3ETg00M]j1?Tg01@;j1FTg01ACj2GTg01B?j2HTg020oj6ITg01E9R0g00D>#1#1#1R1#;#7R2#=R3p-0R4\0R5f1R6f0R7O1X00,40W1W3W2R8P8%11#1#1R1#;R8#7R9%99R:f3R;#DR<f2R=,8930g00C`1>8;%<130f5R1g00e6R8'5p,2fd509%93f6R>%68R8,5>%68,5>3Mf4R>,83301321,28g00\jR11287R?f8R@,32RA,26f;f9RB9L2=,K2'J#CAB2=B;:@[[]7132B,26f:P7O1X00,40[\?^71P7PAP=%AAO3W4W8W5W<W9W;W6X15X33WAX20P4^@0P7P6O1P0P=P7O1X00P=P7C@W:W1X201326,28AE;=6P;P7O1X00,40P7W4W?W5X15X33X20%?990:<%F0p,4segs/G>1H0;30A:>;=P>P7O1X00,40P7W4W>W=W6X15X33X00X20EIo"). Qed.

Lemma to_wall_tail_k_ex : forall ms rest k,
  to_wall_tail ms rest k -> exists ms', k ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "h01kh12msh24resth33ms'p;1p;3p;2g00?Mj10Tg00@2j17Tg00=Bj12Tg00F;j11Tg01Glj36Tg01J\j25Tg01=Zj33Tg025<j34Tg01E9R0g00D>#0#0#0#7#2#1R1p-0\0R2f2R3f1R4f0R536P3P5O1X30,50R6[]0]2]1A3345P6[^02^21^10g02O034o"). Qed.

Lemma to_wallexit_bufs_nonempty : forall bufs code ms,
  to_wallexit bufs code ms ->
  Forall (fun b : list byte => (1 <= length b)%nat) bufs.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h02Hwh14codeh22msh33ms'h44bufsh52Hkh63Hnbh72IHh81bh93bufh:1eh;4resti001xp;1p;3p;2p;4p;6p;5g00?Mj11Tg00@2j19Tg00=Bj17Tg00F;j16Tg02P0j30j25Tg00^0j1?Tg00E[j24Tg00ZQj23Tg02Pkj32Tg00Iej1<Tg02QLj2;Tg00`Mj38Tg01=Zj3:Tg02Qmj4ATg01J\R0j2@Tg02Rnj6>Tg02SOj5=Tg00D>#1#1#1R1#9#7R2#6R3#6R4P3%11#1#1#9#7R1g01E9R5f2R6f1R7f0R830g00e6#?R91428'3X83R:f3R;523[]2]1R<X44%<3?0781;3:W0X25X11f4R==83;?078g00CEf5R;,42,3915=69:7;f6R6=83;923:P8f7R>,42,39f8R915>;5:=P3P:f9R=P9P7P;P=1596P8CAA0=>8X35,@5P0P5f:R0?098X35A23:0P8f<R:?008P:f;P7P8O3W5X35P7P8O2n2001000000120100000b:E>W0W6P7P8O2n2001000000120000000W0X25X11X7<X;4X93P8D=W4o"). Qed.

(* [comment removed for export] *)
Lemma twe_step : forall ms ms' bufs code,
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h02Hwh13Hnbh25Hsteph34Hsvch43bufh54bufsh64codeh72msh83ms'h94resti001lp;1p;3p;2p;8p;7p;4g00?Mj10Tg00@2j1:Tg00=Bj17Tg00F;R0j16Tg01>Sj1ETg01?5j1@Tg00M]j1?Tg00=ej38Tg01@;j1>Tg01ACj2=Tg01B?j2<Tg02P0j31j22Tg00Iej1;Tg02T1j8DTg00`Mj39Tg00^0j1CTg00E[j25Tg00ZQj23Tg01=Zj34Tg01CGj7ATg01G7j4BTg01E9R1g00D>#0#0#0R2#:#7R3#6R4#6R5%02#0#0#:#7R2%E2f3R6#@%?238%>1p,4segsR2f4R7'=1<1638f2R8=167P0P4f0R0f6R9717f1R:f5R;f8R<31]0P7%;4R=?16;P2f7R2P9P=P7P6P8P0GDW0A94:0f9R=712g00CEg00e6#CR21538'3f:R>12:<748A9468f<R871=P01537,32f=f;R=,2774;1539,32f?R212;8R8749P:P2f>P9P8P=P>P0FACBW0W1P:P0O2n2001000000120000000W0X95X44P:P0O2n10110000020020100100P0O1W0W2W3W6W5X81W7o"). Qed.

Lemma msteps_to_wallexit : forall ms ms' bufs code,
  msteps segs ms ms' -> to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h02Hwh13Hmsh23Hnbh33bufh44bufsh54codeh62msh73ms'h84resti001lp;1p;3p;7p;2p;6p;4g00?Mj11Tg00@2j19Tg00=Bj18Tg00F;R0j16Tg01<cj3?Tg02P0j30j22Tg00Iej1<Tg02Tjj7;Tg00`Mj37Tg00^0j1:Tg00E[j24Tg00ZQj23Tg01=Zj35Tg02Uhj6>Tg01G7j4=Tg01E9R1g00D>#1#1#1R2#9#8R3#6R4#6R5%12#1#1#9#8p,4segsR2f3R6f2R73?f1R8=076P0P4f0R0f5R9706f4R:f7R;508]0P6%<4R<?07:P2f6R2P9P<P6P7P0F;W0A7480f8R<702g00CEg00e6#:R=1437'3f9128;757A7467f;R770<P0143:,3=f<f:R<,2:7591432,3=f>R=1297R7752P8P=f=P2P7P<P0E>C=W0W2P8P0O2n2001000000120000000W0X85X34P8P0O2n10110000020020100100P0O1W0W1W5W4X71W6o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h03tr'h11oh22trh31Hh43ms'i003ms'h51nh63Hssh73evsh81kh92msh:2HKh;3Hbmh<1eh=4resth>2IHh?1lh@2sthA2HQhB3HnbhC4HsvchD2HwhE2_HhF2c'hG1mhH4HabshI3Hc'hJ5HconthK4HfdchL2HghM2HhhN2HkhO5HlazyhP3Hn1hQ3Hn2hR3HnohS2HrhT5HstephU2HthV1QhW3_H0hX3_H1hY3_H2hZ5lemmah[5modelh\1xi011xh]2x8i021ci031sp&0p;1p;3p;2p;:p;4p;6p;@p;=p;<p;;p;7p;5p;8g00?Mj1OTg00@2j1wTg00=Bj1nTg01>Sj1aTg01K6k10[Tg00M]k10OTg00=ej32j1cTg01Kmj2WTg00F;j1`Tg01LMk10<Tg00Iej1KTg01MEj3~Tg01N:j1HTg01O4j24Tg01P]k10WTg01J\R0j21Tg02Vkj3@Tg01?5k10JTg01QSj2XTg00>?k20HTg00@Pk10GTg01R5j2_Tg00^0j1mTg01S3k30ETg00ZQj2FTg00o`j38Tg02N7m:04Tg01Glj3kTg01Oij4ATg00E[j2GTg00Zkj30Tg01aJj4tTg00`Mj3xTg00Dcj2]Tg01ajk60ZTg01bhk20YTg01cck20XTg01V9j1^Tg01^6k10VTg01d\m@0UTg00BMj2\Tg01eXk10NTg01f^k20MTg01ggk30LTg005Pj6Pj7pTg01i8m=0KTg01GRj4YTg01ZNl<sTg02Wbj1NTg0049j6oTg01[Ok20FTg01W6j15Tg00CER1j2?Tg0053k60DTg01^Zk30CTg009hj3Lk108Tg02:dj1jTg02X\k30>Tg025Wj4bTg02:5k10;Tg026oj4iTg027fj3hTg007Uk307Tg0079k206j4ITg00:bk205Tg0094k409Tg02;Uk30:Tg02<Mk403Tg02=@k102Tg02=ok60=Tg02>Zm;01Tg029Ik20?Tg028\m:0@Tg02YNk700Tg02?Uk30ATg02@6k40BTg02@Tj5}Tg01G7j4uTg02ZIj6eTg02[Ej7|Tg01@;R2j1rTg01ACj2gTg01B?j2JTg01=Zj3ZTg01kkj1{Tg01m3j1zTg01n;j3yTg01o7k40PTg020;k80QTg02A0m:0RTg02\<k80STg020ok60TTg01U9j2fTf3R3f2R4f1R5'4f0R63@p=>f6R7f5R8g01XbR9f4R:P9P3P4CI;L532/?6p=31G56,F4p=:A0456,]3,f:#^p=<A8345=Z:6p=MP4P9P5P6CIp==P:P9P3A0456CIp=v1456#5p=S1]56,f4#^p=7g01WlR;g01\GR<1478#532A8345=Z:6'?p=EP3P9P4P5CI928:/?6p=91?56,?4p=BP4P9P5P6CI92:3p=RA2;<6p>0I1F45/?6p=V%5692;<p=q1]56,f4p=Q%^5/46p=TP3P9P4P5CI=L96p=;A2345/?6p=C%55=2;6p=df7R=1478#552;A8345=Z:6'?p=DAL956p=6P:P9P3A8456CIp=lAL9569234p=Ug01E9R>g01YXR?P5P6Ctp=[g02];g00D>#O#O#OR@#O#O#ORA#wRB#nRC#aRD&0[5&0OCRE321WCCRF#`&0<4%KFRF32p,2fdRGp,2chRH;~3%w@#nR@#`RIp-0RJ\>RK%H5P4P6O1p,4segsRLP5f:RMf9RNC>RO[^4>14:NRP%`9RQg02^0RRPQP4P@&0WHRSP7P6f;RTP6P5O2RUF3X0Q,1QW1W25@L[[W8W=X9>RVPV&0J3RV1XC452Dg00C`20HB3&0GA32g00e6RA,_8=2CG%aI%mARA,_7%mA,_760E71XI:32A:A@8g00\jRB1FA6RWf8RX9:5@PTP@P@P4PND<P@P4PNPXDM[[]5A:5@NA8@4M#HPTP6O1PLP5fDRYfCRZC>[^4>PLf>R[P@P@P:f<R\D<PZPQP4P@PSf?R]98@=P6fER^P6P5O2F3X0Q,1QX1RX2QC>[[[\W^5B%HXPNP6O1PLP5fBR_fAR`C>[^4>P\PTPMPNPXP=P7P8P:P3N:04Ak\MNPLf=Ra/4_PQP4P@PSP[P6PYP6P5O2F3X0Q,1QX1RX2Qf@RbPQPL14]YRcP5P6CAX@;,1;X7Q1G@TRd=0@TRe9=@SRfP;PL14[ZRgP@PSP@1G@\P\DvP6CAX@;1WCBRhPCPB1_aAPdCt%KhRh3x1]@e1WCI#KPFPFg022b#KPhJ0Z+0YRh-0Xa#^/S_PLPaP_P\PhP_P_PfPbPNPLPaP\P_PGPHPTPdP[p,5Hfd32PXP=P7P4P8&0VdN@0UPb%a?Rd1X?_RH1X?Z92d6X1d1\dH&0NhRh-0M_B0L_h]EPN=0KCYCYPLPgP6P<CAP]PaP\PYP5P<P_P`PbP:P4P6M<sA:6@[PQP4P@PSA0@6[RgA7b@gRgP^PgP@P6P[PaFEE95BWX5B,1BP0PBA:6@]RgPQP3P@PSA0@6]RhDRRHA7`@hRhfFRd'SRG$0IPhP@P6P]P[DMRh3B5BWX5BPQP:P@PSPbP6PdP6fGRf,4_#NO2F3X0Q,1QP6A:6@`PQP8P@PSA0@6`RFA7Z@FRFfHRePFP@P6P`PbFEE95BWP11FA5RF1G@_RiPQP7P@PSA0@5_RjA7Y@jRjfIRkPjP@P5P_P`FEE95V5PQPXP@PSPYP6fJRjP6fKRl,4d#NO2F3X0Q,1QP61FA3Rm1G@^PQPNP@PSA0@:^RnA7f@nRnfLRoPnP@P:P^PYFEE95V:P11G@dRn,F8PQPMP@PSA0@8dRpA7e@pRpfMRqPpP@P8PdP^FEE9PQP\P@PSPeP6fNRpP6fORr,4j#NO2F3X0Q,1QP6A:=@ePQPaP@PSA0@XkRsA7l@sRsfPRtPsP@PXPkPeFEE9P1PQP[P@PSA0@NjRsDRA7o@sRsfQRuPsP@PNPjPkFEPQPbP@PSPoP6fRRsP6fSRv,4p#NO2F3X0Q,1QP6PQPbP@PSA0@ToDRPrP@P@P\PqD<RwfTRxPwP@P\PqPoFEP1PtP@P@PaPpD<RwfURy'4#qPwP@PaPpPqDMPQPYP@PSPtP6fVRwP6fWRz,4s#NO2F3X0Q,1QP6A0@]t9Qs@/Tz#qPvP@P@PbPuD<P@PbPuPtDMP;P<P;PJP6g01]=R<g00W;n0110300021010200X<;g01]ZPxP@P@P`PsD<fYR{'SP5EoP<PQPeP@PSPxP6C;R<fZR|P6f[R},4w#NO2CCX0Q,1Q00F6b3WYWHP5P6O2n2001000000120000000W3WXP5P6O2n2001000000121000000W3WWP5P6O2n2001000000121000000W3WEP5P6O2n2001000000121000000W3X5BP5P6O2n2001000000121101000b<W6X7Qg021mR~PLPcP5%56RcCAPbP[PaP^P4%55PZP_P`P8P3P6M<s1d4G=BHh9BWgX5B,1BP0PBA:6@bPQP:P@PSA0@6bRg%53A7_@gRgPfPgP@P6PbP]GDE95BWX5BPQ16=4P@PSPZP6PkP6P5O2F3X0Q,1QX1RX2Q9@L3P61F6iPQP7P@PSA0@6_Ri%58A7Y@iRiPkPiP@P6P_P`GDE95BWP1PF1G@ZPQP=P@PSA0@5ZRF%57A7^@FRFPjPFP@P5PZP_GDE95V5PQ16T4P@PSPfP6PqP6P5O2F3X0Q,1QX1RX2Q9@L=P6PQPMP@PSA0@:dRF%5NA7e@FRFPqPFP@P:PdP^GDE99V:nP1A:8@fPQPTP@PSA0@8fRn%5MA7k@nRnPpPnP@P8PfPdGDE9PQ16]4P@PSPlP6PuP6P5O2F3X0Q,1QX1RX2Q9@LTP6A:=@kPQP[P@PSA0@XjRd%5aA7o@dRdPuPdP@PXPjPkGDE9P1PQP]P@PSA0@NlRdDR%5[A7q@dRdPsPdP@PNPlPjGDPQ16Z4P@PSPrP6PyP6P5O2F3X0Q,1QX1RX2Q9@L]P6PQP`P@PSA0@TqDRPQP@PSP@P\PpDvRdPL14uwP6%5_RnCAPsP@P@P[PtD<RF/Sz,dZRWPFP@P[PtPrDMRF'?PQ1684P<P|P6P5O2RiCCX0Q,1QX1RX2Q9@LY[]6X7QPL14tyPd%5`CAPnPuP@P@PaPrD<RnPwPnP@PaPrPpGDP1PWPFPQP@PSA0@_xRFP4C;P<PiCCX0Q,1QX1RX2Q9@LYP6PxP@P@PbPsD</S{,d^PyP@P@P`PvD<P@P`PvPsDMP;P~P;P~P6P6Pen0110300021010200X<;%5fAQw@F/T}RF#5P5J0DA2~fFA0@Zy9Qz@f\Ry'T92~eP~fXRZA0@YwRw7Q@f]RY'TRFPLf^Rf,4{A0@^zRv9=@SPcCAPQP@PSA0@k}P4C;P@PSP}P6faRcP6P5O2F3X0Q,1QX1RX2Q9@L5]6XF~PL14ZYA=@Sw%5FCAPLAQ{@v/TfPQP4P@PSA8@e|P6f`RvP6P5O2R{F3X0Q,1QX1RX2QPQP@PSA0@e|P4C;P@PSP|P6P{F3X0Q,1QX1RX2QPrP^P`PaB0C^zpPqO5PQP4P@PSA8@jyP6fbRqP6P5O2F3X0Q,1QX1RX2QP5P6O2P0PQPQP3P@PSA8@k}P6PcP6P4O2F3X0QPQP@PSA0@jyP:C;P@PSPyP6PqP6P3O2F3X0Q,1QP6PQP8P@PSA8@lYP6fcRYP6P:O2F3P1PQP7P@PSP@PoPfDlP5CUfdRfP5P8O2PQP@PSA0@pvPXC;P@PSPvP6ffP6P=O2F3X0Q,1QP6PQPXP@PSP@PpPvDlP3CUPQP@PSA8@rcP:C;fhP8PNO2RcPQP@PSA0@sfP4C;P@PSPfP6fjP6PTO2F3X0Q,1Q[X2QfgP:PXO2PQPQP@PSA0@uYRfP@PSA8@uYRuP7C;C;RsA=@SYRr/66fiP6PMO2CCX0QP8PQA0@tqRv9=@SRpA8@tqRo9=@SR1/68'6RlA=@SqP8CUPcAL@voRc=2IqPQ%cQRy%jQ:0>QyPs16r7AL@fuRu9=@SRf/67PQ\QRj\QR}PQPjPyPQPQPyPyCbR0CbRzPQPjP0PQPQPy&0;QCiCi9h}z&089PrPfP9\@RfPQ^?I%c9Rr:07@9RzPIPQ%cIR}PyCb206@9205@9PSPfPzP@P9Pr%j9H09:0:fz9hfzPSH03PYPuPIP}&02IPuPYP6J0=N;01P7P720?Q7N:0@K00WZB0A@tqPQ16p1RqPQPsP6P7CUX?QPQPlA2Qs6X?Q1\Ql16q8P9PpP1P8H0BEoA=@ScP@P9PSPvPoD}EPO2P6CuCYWAPNP6EPW3P5P6O2n2001000000121000000W3X0QP5P6O2n2001000000121101000W3X1RX2QEeW6PkP6P=FpW3P6O1b3WEWIP5P6O2n2001000000121000000W3W6P_P6PbFpW3P5P6O2n2001000000121000000W3WQP5P6O2n2001000000121000000W3XPmP5P6O2n2001000000121000000W3X5BP5P6O2n2001000000121101000b<W6WFX7QF|bDW:W;W>WJWBWSWLWRWCX8KX=IX]CX9>PJ^\>P6P5O1%K@RJ#HP3P6O1PO[^4>PLPPPXPQP4A=@SJRJ/66RPPUCCX0Q,1QX1RX2QP6P:P4O2PMP5P6O2PQPQP3PPP\P6P4O2CCX0QP416J4RJ92Q4PTP4P5O21\QJP6CuCYWAX1RX2QEeW:W;WNW8X9>A:A@5Ak345%H3P:P6O1PLP5P\PTC>[^4>PLP7PTPQP4P@PSPXP6PaP6P5O2F3X0Q,1QX1RX2QC>[[%H:RAP8P6O1RJPLP5PaP\C>[^4>P4P5P6O2RPW:W;W>WDWBX8KX=IX9>A2DVE%r>RV1gL:1J>332AZ:34PLP5P[PaC>\J^4>PLP=PaPQP4P@PSPNP6P]P6P5O2F3X0Q,1QX1RX2QC>[\A%H8P7P6O1PLP5P]P[C>[^4>PL14N[PQP4P@PSPMP6C;RMPbP6P5O2R7CCX0Q,1QX1RX2QRA%K9R914X[RaPLPNP[PXP[P\P81W>?R8#rRJP2P>PJ1gLNRE1[6],J8%{8RD%z8RUn10110100031010000001[N],J8R]92J6XGJPV1J>XP2P>PJP61[6b,J8PDPUn1011010003101000000=2J]XGV1[X[,J8,\JPEP:EPAyLN[PLPNP[PTH0PEPL0QPL14TbP5P6CAPLP\P`PTP4P5P[PXP=P6N:0RW6X@;X7QPLPaPAPQ1694PMP7CCX0Q,1QX1RX2QPPPQP4P@PSP\P6P_P6P5O2F3X0Q,1QX1RX2QP5P6O2P6PQ1693P@PSPTP6P`P6P4O2F3X0Q,1QeW3X1RX2QEeL0SW:W;W>WUWTWCX8KX=IX4>X9>J0TWKWOWMWVX[?o"). Qed.

(* [comment removed for export] *)
Lemma to_wexit_nil_exec_aux : forall ms bufs code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms bufs code ->
  bufs = [] ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h01oi001oh12trh22msh31Hh44bufsh54codeh65Hbufsh74Hsvch83Hssh93Hteh:2IHh;1eh<3evsh=1li011lh>1mh?1nh@2sthA2x8hB2H0hC5HconthD2HghE2HhhF5HlazyhG3HnbhH3HnohI2HrhJ5HstephK3Hx8hL1bhM3bufhN5modelhO3ms'i023ms'i031xp;1p;3p;2p;4p;6p;=p;:p;5p;8p;9g00?Mj17Tg00@2j1]Tg00=Bj1NTg00F;R0j1=Tg01>SR1j1aTg01K6j1CTg00M]j1rTg00=ej30Tg01Kmj2@Tg01LMj1iTg00Iej15Tg02^jj4DTg01O4j22Tg02_cj1`Tg02Vkj3BTg01?5j1HTg01QSj2:Tg02`Vj1UTg01R5j2;Tg014Qj14Tg00@Pj1FTg00@nj2JTg02aPj3LTg02b5j2GTg00BMj2?Tg01W6j1hTg01Oij4KTg01ajj6gTg02boj3fTg02cej1eTg02d\j3dTg005Pj68Tg02e^j3cTg02f^j2OTg02gal=bTg0049j6ITg02hUl:}Tg01[nj1MTg01[Oj2_Tg02iSj2|Tg02jVj1{Tg02kLj1\Tg02lFj3ZTg02mAj1zTg01G7j4[Tg02n8j2yTg02nVj5xTg02\<j8YTg00>?j2vTg00^0j1WTg01S3j3uTg00E[j2ETg00ZQj2ATg00Zkj3VTg00Dcj2TTg01U9j2PTg01V9j1QTg00`Mj3>Tg01@;R2j1STg01ACj2RTg01B?j26Tg01kkj1qTg01m3j1pTg01n;j3oTg01o7j4nTg020;j8mTg02A0l:sTg02ZIj6tTg02oMl9lTg030Hj2XTg00CEj2wTg009hj3kTg01aJj4jTg01XbR3f2R4f1R5'Xf0R63>p=^f5R7f4R8f3R930AZ456'wp=1%`5,X4=>36p=3Ak356p=9g01E9R:g01YXR;P5P6Cjp=<g00D>R<#7#7#7R=#]#NR>#=R?#=R@%7=#7#7R=#]RA#NRB%aBRC%C6%rBRD301@BBRE#=%i5%5ERE30p,4segsRFP7P8P9CDPF%5?RG90@5f7RH,29%=3RIg02^0RJPIP5f9RK#`RL%53RM5^9P9P5P6E1W0W15BF[X5BX4@X2:%H51:B650C%U5A0@GGPFf8RN,28PIP5f6ROg00e6RP';RQ%4<#4#4#4#4#4#4#F,JARR5LARSf:RT;3MRUPSP5P6E1X0JX1I1;8P=LARRV?3NMRW1GVNRX,28RY1?IWRZA3VXM,9M=0IWR[eP[PI1;7P=LARRR1GRKR[;3M,9MPF12OTR\P61GST,2O#hCKX=IPFP7PKP8g00T^,JA1@B?#5PEPEg022b#5g00\jRE,@B#5EgP[PMPRPNP9AfF78R]PBP8%U6XLBP4%e]AdF78E87cK1:BRR],?C%C[=0C]e1ORKM=bA^RLMRLP6EIb3g01WlR^PFP\P5P6CKPFPHf;R\POP4P5PTP7P8P6M:}W8W@X<IPFPYPI19U5R_PUPSP_P6E1X0JX1IPC1:BVR_A0C6D#MX0CA0C_DRSPCP]P1PBp-0R1P6g00W;RUg01]=R`n10110000021000000X;Cg01]ZRaPDP6EIP`1_`6bBW3%MSe%CXRS1|VNRbE8%{Y#C=0CD#MePIPWPIP6PLPRP6127[#\E1X=IA0IWW%\YRY9ZVWR[PZA0CS_%zX=0CDPCP_A0C6]X0C1?C_PSPbE81OVNC[P[eC[19WMR[1y3WE8PIP[PWPVP[PYE1eDxGYW6WKW7XABX2:%H81:B950Cg00C`1vA8%F=30%F<,JA90BQ%a?%WPRP,;H%WP,;H5uH1:?7301E>O,AP1AP6RP1E>K,A5PFf<RQAV>4T,T>'P#QPKPNCD[[^?E1E>T,A5A0@TGf>RAAV>9Q,T>'P#QfB'2PIP5fD=3QMPQP5P6E1X0JX1I5BF[[\P^?EA>?KN=0@GP@A>?TKP0P?P1P6P`PUn10110100020020000000X;@PaPGP6EIP`f=R`fA'2PIP5fC=3\MP\P5P6E1X0JX1I5BF/_6b3W6W:WCWGWIWDWHW7X5BX4@XM?XABX2:%H9=0CD%S:RD1RF816:930PFP8P9P4CDA0@8G12O\PIP5A3O`MPOP5P6E1X0JX1I5BF[A0@7GPF12NQPIP5A3HAMRGPHP5P6E1X0JX1IRCPM12HQR?PFPNPQPHPQP\P81@:;Ra#SRUP2P:PU1RFNR11<6`,6a%qaR0%paREn10110300031010200001<N`,6aRP90U6X>UPD16:HP2P:PUP61<6A,6aP0PEn1011030003101020000=0UPX>D1<HQ,6a,?UP1P9E8AoFNQPFPNPQPTCnE8GmPF12TAP5P6CKPFP\f?R\PTP4P5P`PHPOP6M:sW8X@^X<IPFP?PCPI19M5RCPGPHPCP6E1X0JX1IP5P6O1PIP5f@=3KMPKP5P6E1X0JX1IP5P6O2P6PI19M4R4A3N\MPNP4P5E1eW3X0JX1IEtGYW6W:W9WJW7X5BX4@XO:X2:POP7P8P6M9lW9WFWEXN;W5W4X2:o"). Qed.

Lemma to_wexit_nil_exec : forall ms code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms [] code ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "h02Hhh15Hlazyh23Hteh34codeh45modelh52msp;1p;3p;2p;4p;8g00?Mj10Tg00@2j15Tg00=Bj12Tg01>Sj16Tg01K6j1=Tg00M]j1;Tg00=ej33Tg01Kmj28Tg00F;j11Tg01LMj17Tg00Iej14Tg02^jj49Tg00BMj2:Tg031>j8<Tg01E9g00D>#0#0#0R0#0#0#0#5#2R1g01YX%61f0R2#=%;1331811R1#1f1R3#7%4133p,4segsf4R1%50#2#1R0#4R4f3R5C9f5P4P1P5f2P3P2%10/:4G<W2W1W0W4W3W5o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h02trh11oh23tr'h31Hh42msh53Hbmh62Hwh74codeh81lh95modelh:4resth;1Ah<4Hfdch=2Hhh>5Hlazyh?1Ph@1ahA4bufshB1khC3ms'hD2HbhE3HbshF3HeqhG2HkhH3HnbhI2HxhJ2IHhK3bufi001xp;1p;3p;2p;6p;4p;5p;9g00?Mj1<Tg00@2j1UTg00=Bj1MTg00F;j1>Tg01>Sj1iTg01K6j1eTg00M]j1_Tg00=ej32Tg01Kmj2\Tg01LMj1[Tg00Iej1GTg01MEj3XTg032Cj1KTg02P0j3Dj2ITg01O4j2;Tg02lFj35Tg02Vkj3=Tg033>j6^Tg00`Mj31Tg00^0j1]Tg00E[j2OTg00ZQj2NTg01=Zj3HTg02Pkj36Tg00CER0j23Tg034?j4ZTg01N:R1j1ATg01P]j1YTg01J\R2j2FTg01Glj3WTg02_cj1JTg034cj5VTg025<l9hTg035cj27Tg00BMj2fTg02@6j4dTg0049j6cTg005Pj6QTg01G7j4`Tg02ZIj6aTg02SOj5bTg030Hj2PTg009hj3:Tg0079j4STg01XbR3f2R4f1R5#J'Pf0R631p=0f5R7f4R8f3R9/74=:3532/36p=Cf7R:f6R;1778=:3932A5456'3p=4P9P3P4P5CS=:36p=9A2945/36p=@17891P45=1365:3p=LA2789A5456'3p=EA:3569294p=?A5456,39p=TP4P3P5P6CSp=BA:356p=81745=:36p=RA1456,79p=gg00D>#<#<#<R<#U#MR=#>R>#>R?P>%<<#<#<#U#MR<g01E9R@g01YXRA%i<%e6%_<32RB1\<<RC#>%[5%GC32RCp,2fdp,2chRD;X4RE%K;AD:;7p,4segsRF1;;7RG%>3RHg02^0RIPHP5PDf:RJf9RK%G3RL70:RMA5K56RNECW1W03=[[[[[]9]4]7ROXA?%G>RP#KADP;7P;P:P7P8P9P6E^PHP5PDPPPMPNECX1IX0H9=FGeW6W5X<EX>CX=BX9AX4@X7<f8RG=1>:#KA1>KG?D;7P0g00e6#]RN1O=J'N1IK:9H;J1;:;PHP5PDf=RMf<RP51>A0JGLPJP5P6G4X1IX0H5=FP61O=P,NN1IPJ9HKMg036\p4p710RNp-0RQ\6RR%>4RSP0A19569694P9P4O1A6895'3[RTP4P5O1A6946'3A18459689RU[P8P9O1A6784'3\UP9P4P5P6CZP5n2001000000120000000W8X@5W?W;PT^8S^@5^?R^;NP6P>P1f?RNf>RRP;O5%ANA6>1R'3P0f@RS#AA6>1N1;MPPHP5PDfCRTfBRU51>A0SRLPSP5P6G4X1IX0H5=FP6%AUA6>1UPF1;SNPHP4P=%YDR1fGRVP6C9PHP5PDfHRWfFRXfDRY;0LPXP5P6G4X1IX0HP6P5O2C@X2H,FHX1IX0HPHP5PDfERZ91>XfAR[=0TLR\A5T56R]ECX1IX0HPQ\@RQAW456%A4P9P6O11;5XPHP5PDfLR^fJR_?0WLP_P5P6G4X1IX0H5=F[^C@1;7ZPHP4P=P1P:P6C9PHP5PDfNR`P^%J_PLDLRaP^P5P6EEX1IX0HP6P5O2C@X2H,FHX1IX0H5=F[[RF[]B^:>^4@AH456PF[^BQ^:>^4@PNPHP5PDPZP\P]ECX1IX0HPRPMPPDVPSPY1IT[P;P5ADYU6PYPTP5P[PSPNPRP4P6O8WGXC@M9hPHP4P=P1fIRRP6C9PHP517D_A0WXLC?RXPWP5P6CTX1IX0HP6P5O2C@X2H,FHX1IX0HP5P6O2P2PHPHP9P=P1PWP6C9PHP6PDPVA0ZTLRTPZP6P4G4C@X2HPHP9PDA1>WVPTPZP9P4G4P6PHP7P=P1P_P6C9PHP6PDPRA0VZLPVP6P8G4C@P0PHP;fKRZ9B=1P5C?PXPWP5P7CTPHP:PDA1>^ZA0RVLPRP:P;G4P6PHPGfMRV9B=1P9C?PHP=P1P`P8C9A2H7aRaA5^7KR7'3PHP5PDfPR9fORW51>PV%JZPLDLRXPVP5PJEE[X0HPHP8PDPVA0ZRLPZP8PGG4P0PaP7PHP=P1P9P;C9R;PXPVP;PJEEP6PHP:17D9A0`^LC?A5WGPfSRP9B=1RG/8KR^fRR:91>PA09`LR`5RDRJ52HA59^MPH17D:R:/8`R^PHfTR99B=1R1/86PDP>P9PPCgfQ?0WLRWC?X2HPH18G^R^ARDPW,81=2H6X8H1fH^18G:/8`P3PGP:P`CdEcA2H^JePKP5EQP6C`WIWFP5P6O2n2001000000121000000W3PKP6EQW3P5P6O2n2001000000121000000W3X2HP5P6O2n2001000000121100000W3X1IX0HEaWEWDP5P6O2n2001000000121000000b5b3W6WHP5P6O2n2001000000121000000W6W5X<EX>CX=BX9AX4@X7<XJOX:?XK>P6DbWAo"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h01ci001ch11oi011oh22trh31Hh42Hmh52Hxh63Heqh72c'h83Hbmh94Hfdch:2Hhh;5Hlazyh<5Hstarh=2Hwh>2_Hh?1ah@4bufshA4codehB1ehC5modelhD2mshE1xi021xp;1p;3p;2p;9p;4p;7p;8g00?Mj1<Tg00@2j1ITg00=Bj1DTg00F;j1>Tg01>Sj1VTg01K6j1?Tg00M]j1RTg00=ej37Tg01Kmj2QTg01LMj1OTg00Iej1BTg01MEj3KTg032Cj1JTg02P0j3UTg01O4j20Tg0379l9TTg0389j4STg0397j41Tg00CER0j25Tg01J\R1j2=Tg01_Zj43Tg02kLj16Tg02lFj3:Tg00BMj2PTg039oj7NTg02jVj1ATg01[nj1@Tg01GRj4MTg005Pj8LTg02Wbj1;Tg035cj2CTg02_cj1HTg030Hj2ETg00`Mj3FTg009hj3GTf6R2f5R3g01XbR4f4R5f3R6'Cf2R7f1R8#H'Ef0R95F43G37p=8A:789,56p=21C56%H8,E7=F495G4p=4g021mR:/=9p=9g00D>#<#<#<R;#I#D#>#>%<;#<#<#I#DR;g01E9g01YX%V;R<%?9%R;R=371Q;;R;#>%O8%B;37p,2fdp,2chR;;K7%J2f7R>?U23p,4segsR?1023%>4R@g02^0RAP@P8P;f:RBf9RCP>%B4R4F8PCP8P9C2W1W2f8RDP>P2P3P5P6P7P8P9M9TCSP?10D>P8P9C1P@P8P;f<REf;RFPCP4F8PFP8P9C2X1AX2@P8P9O2'5X1A,=AX2@,=@P1P@P?10CDRGP8P9C1P;PFPBPDP4D4RH97@8PBP8P9C2'5X1A,=AX2@P?PGPHP9C3X0:#9P9P?10FBP8P9C1P@P8P;f=RHPEPBP4F8PEP8P9C2'5X1A,=AP1PAP?10EFP7P9C1P@P7P;f>R1PHPFP4F8PHP7P9C2'5X1AP?10HEP;f?R7P1PEP4D4P9C3X0:#9P9PAP?1071P3P9C1P@P3P;fARGf@RIP1P4F8PIP3P9C2'5P?10GIRJP;fCRKfBRLPIP4D4RMP9C3X0:#9[P9P?10I7RNP2%69ROC1P@P2P;PLPGP7P4F8RPPGP2POC2'5P0P?PJP>%68ROC1A7@>MRMPLP>POC2P?10KLROP;fERQfDRRPLP4D4P9C3X0:#9RSP9P?POPC%66C1P@PBP;fFRTPQPKP4F8RKPQPB%65C2P0P@PFP;fGRUPTPRP4F8RR%639:TFP?10UTP;fIRUfHRVPTP4D4RWP9C3X0:#9RXP9A7@HWRW%6D9:U1P@P;fKRHfJRYPVP4D4RZP?10YUP9%6BR[C1fLR\%6FR]7:8P?fMR^/0\P;fOR_fNR`P\P4D4P9C3X0:#9]5]4X2@P?10UVPZ%6CC1P;P\PHPUP4D4=:H[P?10HYR[P;P^P\PYP4D4RYP]P8PF1PA]FNP?P[PYPFC3%AF#?=7<=#@'5P0P?10\HP;P`P^PHP4D4PEC3%AE#?=7<=#@P?10`^R`P;fPREP_P^P4D4R^P9C3X0:#9P9P?P`P^P1C3%A7#?=7<=#@P:P?fQ/0EP;fSfRPEP4D4P9C3X0:PIP8CMW>W<P8P9O2n2001000000120000000b?W5W4P7P8P3P9GLW5W6P8P9O2n2001000000121000000W3W4P8P9O2n2001000000121000000W3X7:P9O1P?PNP2%;9RNC1PPPGP2PNC2'5P0P?PJP>%;8RJC1PMPLP>PJC2PSP9P?POPC%;6C1PKPQPB%;5C2P0PR%;39:TFPXP9%;D9:U1g01]=P?P[PYP9C3X0:#9P9n010000000W5X6WP8P9O2n2001000000120000000W3W4P8P9O2n2001000000120000000W3X7:P9O1n0110100021110011100XEAP8P9O2n2001000000121102000W3X2@P8P9O2n2001000000121102000bBW=W8W9W;W:WCWDWAW@o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h01oi001oh11Hh22trh33Hx'h42_Hh52Hxh62Hmh72c'h81eh93Hbmh:3Hexh;4Hfdch<2Hhh=5Hlazyh>3Hneh?2Hwh@4bufshA4codehB5code'hC5modelhD2mshE1xi011xi021bi031cp;1p;3p;2p;9p;4p;7p;6g00?Mj1<Tg00@2j1DTg00=Bj1@Tg00F;j1>Tg01>SR0j1WTg01K6j1:Tg00M]j1OTg00=ej30Tg01Kmj2KTg01LMj1ITg00Iej1ATg01MEj3FTg032Cj1ETg02P0j3VTg01[nj1CTg01O4j22Tg02lFj1Bj39Tg02Vkj3UTg0379l9NTg0389j4LTg0397j44Tg00CER1j25Tg01J\R2j2=Tg02kLj16Tg03:oj7JTg02jVj17Tg01QSj28Tg02mAj1?Tg0049j6HTg0053j6GTg03;jj4MTg02Wbj1;Tg035cj2PTg02_cj1QTg030Hj2RTg00`Mj3STg009hj3TTf6R3f5R4g01XbR5f4R6f3R7'Pf2R8f1R9#Q'Rf0R:5S53T30p=3A989:,57p=1g00D>#<#<#<R;#D#@#>#>%<;#<#<#D#@R;g01E9g01YX%W;R<%::%O;R=301K;;R>#>%I9%A>30p,2fdp,2chR>;F8%E3f7R??V34f8R@90;:#Cp,4segsRA12@?%B93URBPAf9RC/2@%>5RDg02^0REPDP9P>f=RFf<RGf:RH%A5R5F3PGP9P:C1W0W2f;RIPHPCP@P?P3P4P6P7M9NCLPA12IHP9P:C4PDP9P>f?RJf>RKPGP5F3PKP9P:C1X0EX2DP9P:O2'5X0E,=EX2D,=DP2PDPA12GIP9P:C4PDP9P>PKPFPIP5F3PFP9P:C1'5X0E,=EX2Dg01]=RLP:PA12KFP9P:C4PDP9P>f@RMPJPFP5F3PJP9P:C1'5X0E,=EP2PEPA12JKP8P:C4PDP8P>fAR2PMPKP5F3PMP8P:C1'5X0EPLP:PEPAfBR8/22P4P:C4PDP4P>fDRNfCROP2P5F3POP4P:C1'5PL[P:g021mRPPA12O8RQP3%6:RRC4PDP3P>fERSPNP8P5F3RTPNP3PRC1'5P1PA12NORRP?%69RUC4PDP?P>fFRVPSPOP5F3RWPSP?PUC1PLP:PA12VSRUPC%67C4PDPHP>fIRXfHRYPVP5F3RVPYPH%66C1P1PDPIP>fJRZPXfGP5F3R[%6499XIPLP:PDPFP>fLR>fKR\PXP5F3R5%6@99>KPA12>\%BSPOPJ%6CROP4FJA9SJOP1%7HRO#:fN,8;RJ50<%?O=0<=PLP9%7G#:fPRG,8;50<%7F#?=0<=P1%7KRF#:18;Z50<%?F=0<=PLP6%7M#:18;>50<%72#?=0<=P<%78#:fOR8,8;R=90<:X0<P9fV,8;R2P4EHA0<2JP<P;P0P;P;P:P:fXR0n10110000021010200X8<fWR<,8;P=P:EGA0;<8A0;0GPGP;fYfQP:CMO1W3P:O1b1b3W4W3P9P:O2n2001000000121000000W4W5P9P:O2n2001000000121000000b3W5W4P9P:O2n2001000000121000000W1W6P9P:O2n2001000000121000000W1W7P:O1PAPQP3%;:RQC4PTPNP3PQC1'5P1PAPRP?%;9RRC4PWPSP?PRC1PLP:PAPUPC%;7C4PVPYPH%;6C1P1P[%;499XIPLP:%;@99>KPLPLP:n010000000W5X45P9P:O2n2001000000120000000W1W6P9P:O2n2001000000120000000W1X7PP:O1n0110000021110310103XEEP9P:O2n2001000000121101000W1X2DP9P:O2n2001000000121101000b8W:%CBeW>XB;W?W9W;W=W<WCWDWAW@o"). Qed.

Lemma to_wallexit_trace_unique : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall tr', tr' <> wevents_ch ch bufs ++ [ExitEv code (m_fs model)] ->
  ~ OmniRun.exec segs (mkCfg ms model) (fun tr _ => tr = tr').
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h02trh11oh21Hh33tr'h43Hbmh53Heqh64Heq'h73Hexh84Hfdch92Hhh:5Hlazyh;2Hmh<3Hneh=2Hwh>2_Hh?4bufsh@4codehA1ehB5modelhC2msi001xp;1p;3p;2p;9p;4p;7p;6g00?Mj17Tg00@2j1CTg00=Bj1ATg00F;j19Tg01>Sj1STg01K6j1QTg00M]j1PTg00=ej36Tg01Kmj2LTg01LMj1HTg00Iej1@Tg01MEj3ETg032Cj1DTg02P0j3RTg035cj25Tg01[nj1BTg01O4j21Tg02Vkj3OTg02lFj30Tg0379l9NTg0389j4MTg0397j43Tg00CER0j24Tg01J\R1j28Tg03:oj7KTg02_cj1<Tg00BMj2JTg005Pj6GTg0049j6FTg030Hj2>Tg00`Mj3=Tg009hj3?Tg01XbR2f2R3f1R4#<'>f0R53=p=;f3R6A?245763p=:f7R7f6R8f5R9f4R:'5%<3,>6==245?236/45p=215:61>34==255?2p=Ig00D>#7#7#7R;#C#A#9#9%7;#7#7#C#AR;g01E9g01YX%S;%Q5%P;361L;;R;#9%H4%@;36p,2fdp,2chR;;E3%D8AR789%92R<P<P5f9R=,5;f8R>%@2R27;8C:#Bp,4segsR?11>7g02^0R@A6<46UX0<3ORAP?11=>P<P4P;f=RBf<RCf:RDP2A0C45G2X1@X0<f;REPDP=P>P7P8P9P:P6M9NCMP?11EDP4P5C3P<P4P;f?RDf>R8PCP2A0845G2X1@X0<P4P5O2'4X1@,8@X0<,8<P1P<P?11CEP4P5C3P<P4P;P8PBPEP2A0B45G2'4X1@,8@X0<g01]=RFP5P?118BP4P5C3P<P4P;f@RGPDPBP2A0D45G2'4X1@,8@P1P@P?11D8P3P5C3P<P3P;fARDPGP8P2A0G35G2'4X1@PFP5P?11DGP:P5C3P<P:P;fCR1fBRHPGP2A0H:5G2'4P0P?11HDP9P4C3P<P9P;fDRHP1PDP2A0194G2PFP5P?11H1P7P6C3P<P>P;fGR6fFR7PHP2A07>:G2P0P<P=fH,5;fER0=;62C:A06=9PFP5P<PEfJRE,5;fIRF?;62C:A0EC>P?11EFA6<40V@X0<R0PDPBP=P9FKP0PBP=O2P1P<P8P<P5fN,5;fMR1fK;;2C:R=X3<P<P;P1fL%<EP2DIR2P=X0<1J<2P8P3EGPHP5EFO1b6W>W5P4P5O2n2001000000120000000W2W;P4P5O2n2001000000120000000W2X1@P4P5O2n2001000000121100000W2X0<P4P5O2n2001000000121100000bAW7%BAeW<W3W=W4W8W:W9WBWCW@W?o"). Qed.

Lemma to_wallexit_not_silent : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  ~ cosafe segs (mkCfg ms model) (fun tr => tr = []).
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h04Hnilh15Hstarh21ei001eh31Hh41ch51li011lh63Hbmh72Hch84Hfdch92Hhh:5Hlazyh;2Hwh<4bufsh=2c'h>4codeh?2e0h@5modelhA2mshB2tri021xp;1p;3p;2p;9p;4p;7p;6g00?Mj13Tg00@2j1ATg00=Bj1>Tg00F;R0j16Tg01>Sj1OTg01K6j1LTg00M]j1JTg00=ej32Tg01Kmj2FTg01LMj1DTg00Iej1;Tg01MEj3CTg032Cj1BTg02P0j3NTg01O4j21Tg03<Fj3MTg03=?l9KTg035cj25Tg01_Zj44Tg01J\R1j2ITg03>Fj7GTg02_cj19Tg0049j6<Tg01[Oj2ETg01[nj1HTg030Hj2?Tg00`Mj3:Tg009hj3@Tg01XbR2f3R3f2R4f1R5#9'?f0R65:23@p=01?45=:26p==A@256p=7A:256p=8g00D>#3#3#3R7#A#>#6#6%37#3#3#A#>R7g01E9g01YX%O7%L6%J7321F77R7#6%D5%;732p,2fdp,2chR7;C4f6R8#Bf7R9f5R:7N8p,4segsR;118:%62R<%;2R=92<6WBR>3MR?f9R@f8RAP9P8P:f4R8P3P4P5M9Kg021mRBP;11A9f:RC,57P@P9P=C0P6C4X4B'IP1PBP;11@Af;R@,57PCPAP=C0P6C4X4Bg01]=RAP6P;11@Cf=R1,57f<RDPCP=C0P6C4P;11D@P>f>RD,57P1P@P=C0R@P5P:P6FGP>P@O1f?R@,57P<P0P2P;11@Df@%9D;==R7,76P8C4fAR8%9@;==R>,75=2<=PA]0]1P6P;11D1P=P@P1P=C0P3C417=7=2<=P<17=>P0P2p-0P6PAg00W;n10110100020020000000R0X2<g01]ZR>P=P6E<PA1EA6R7b3W0W1P;fBR;/181856fCR1P8P=C0P9C41845fDP;P=C0=2<=P<1834fEP1P=C0P0X?<P>P=P6E<PAP7b3W0W1X5<X22P5P6O2n10110100020020100101P4P5O2b5b0W1X=BP5P6O2n2001000000121102000b2W7%H?eW;W6W8W:W9W@WAW>W<o"). Qed.

Lemma to_wallexit_star_only : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (m_fs model)]).
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "p'0h01oh12trh23tr'h31Hh42_Hh52HQh63Hbmh73Heqh84Hfdch92Hhh:5Hlazyh;5Hstarh<2Hwh=4bufsh>1ch?4codeh@1ehA1lhB5modelhC2msi001xp;1p;3p;2p;4p;9p;7p;6g00?Mj14Tg00@2j1ETg00=Bj1?Tg00F;j19Tg01>Sj1STg01K6j1PTg00M]j1OTg00=ej38Tg01Kmj2JTg01LMj1ITg00Iej1=Tg01MEj3GTg032Cj1FTg02P0j3RTg01O4j2DTg01_Zj4QTg0379l9NTg03?Bj7MTg0389j4LTg0397j43Tg00CER0j25Tg01J\R1j27Tg00fAj36Tg035cj2:Tg02lFj3;Tg00h1j3KTg0049j6HTg02_cj1ATg030Hj2@Tg00`Mj3BTg009hj3<Tg01XbR2f4R3f3R4':f2R5f1R6#A'@f0R75B23<p=1f5R8?834A;567'5p=2A<267p=0%A6,@5=B27p=>A<2679845p=Cg00D>#4#4#4R9#E#?#9#9%49#4#4#E#?R9g01E9g01YX%S9%P7%O9381J99R9#9%I6%=938p,2fdp,2chR9;G5f6R:#Ff7R;?R:8%92R<g021mp,4segsR=f8R>/D;P6P7CQP=P6g02^0R?P<P6P9f?R@f>RAf<RB%=2RCD1PAP6P7E2X0?X1<1036P7O2W0X2<P=f9RD/D>P<P6P9f=REPBf:RFPCD1RGPBP6P7E2X0?X1<P5P6f;RHPFPDP>P;P:P8P3P4M9NP7FMCLP=P4P6P7C3P<P6P9fARIf@RJPAPCD1RKPJP6P7E2X0?X1<10:6P7O2X0?X2<P6P7O2'5X0?,7?X1<,7<P1P<P=P3P6P7C3P<1086RLP9PAPEPHPCD1PEPLP7E2'5X0?,7?X1<A623GP7P=P:P6P7C3P<10;6R:P9PJP@PEPCD1P@P:P7E2'5X0?,7?P1P?P=P;P5P7C3P<10>5R5PKPJP5P7E2'5X0?A62>KP7P=PDP3P7C3P<10F3RKP9fCR5fBR1PJPCD1P1PKP7E2'5P0P=PFP8P6C3P<10H8RFP9fDRKP5PIPCD1P5PFP6E2P9fERFPKP1PCD1962BP7P=PBP;P4C3P<10A>RAP9fGR4fFR;PKPCD1P;PAP3E2P0P<10@DRDfHR@,:9A>4FCCCA;4D8P9fIRDP@P;PCD1962JP7P<10IHfJRI,:9A>D4CCC101B=;I>P<105EA62K7XA<AK25EP9fLfKPDPCD1P6EHW4W7P6P7O2n2001000000120000000W5W4P6P7O2n2001000000120000000W3X0?P6P7O2n2001000000121100000W3X2<P6P7O2n2001000000121100000b@W;W>W1W<W6W8W:W9WBWCW?W=o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"; "WithSegsCh"] "h01oh12trh21Hh33Hbmh44Hfdch52Hhh65Hlazyh72Hwh82Hxh92_Hh:4bufsh;4codeh<5modelh=2msp;1p;3p;2p;9p;4p;6g00?Mj10Tg00@2j1<Tg00=Bj1;Tg00F;j17Tg01>Sj1JTg01K6j1DTg00M]j1CTg00=ej31Tg01Kmj2@Tg01LMj1?Tg00Iej19Tg01MEj3>Tg032Cj1=Tg02P0j3ITg01O4j2HTg035cj23Tg02_cj14Tg030Hj26Tg00`Mj35Tg009hj32Tg02lFj38Tg00CER0j2:Tg0379l9BTg03@<R1j2ATg03A9j4ETg02ZIj6FTg03BAj3GTg01E9g01YXg00D>#0#0#0R2#<#;#7#7%02#0#0#<#;R2%J2f2R3#D%C2311@22R2#7f3R4#?%9231p,2fdp,2chR2f4R53>%=5f5R6f7R77I5p,4segsR8f8R9/H7R:P8P:g01XbR:#7R8g02^0R;f1R<1329f9R=#4,67%9:R>55:52:518f0R?987<':W0W1P1f6R1P6P9P7P5P4P3P<P?M9Bf:R7,32f;R@#4,6==5:>52:918<A8=<?':X0;X18P<P?O2P0132=%47,69=5:>52:9183A893<1A43P?132@f<R2#4,67=5:>52:9185A8@65P2P1P6P?CEW8W9P<P?O2n2001000000120000000W2X0;X18EF3GW7W3W4W6W5W;W:W<W=o"). Qed.

End WithSegsCh.

(* [comment removed for export] *)
Abbreviation wexit1 segs ms bufs code :=
  (to_wallexit segs (Z_to_bv 64 1) bufs code ms).

(* [comment removed for export] *)
Lemma wevents_ch_fd1 : forall bufs,
  wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h04bufsh12IHh21bh32bsh41lp;1p;2p;3p;4p;6p;5g00?Mj10Tg00@2j19Tg00=Bj1;Tg00F;j14Tg00@Pj1@Tg00@nj2<Tg035cj23Tg03C?j11Tg00=ej32Tg00Iej18Tg00BMj26Tg01P]j1:Tg0079j47Tg009hj35Tg005Pj6?Tg00`Mj3>Tg02SOj5=Tg00D>R0#0#0#0R1#9#;R2#4R3#4R4P3g01XbR5#4R6%01#0#0#9%@0'<R0f0R1'3%1132R7X04%85,66%83R8,30%18526eP6f1R8#1R9P2P5%:0R:f3C7R;=551f2R<#1955;526X46P2P5P:P<C7=559,661308P1E?A>3<8R<,30%1<526eX17X34X23P1D=W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wall_omni_run : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit segs fd bufs code (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]
                 /\ exits_with code tr o).
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h03Hbmh15Hfd32h24Hfdch32Hwh44brk0h54bufsh62chh74codeh82fdh93inph:3limh;2mbh<1oh=2pch>2phh?3rndh@4segshA2sphB2trp;1p;3p;6p;9p;5p;2p;=p;4g00?Mj10Tg00@2j1<Tg00=Bj1:Tg00ATj1?Tg00=ej32Tg00F;j11Tg03D5j14Tg03E3j65Tg01MEj3ATg032Cj1@Tg03Elj13Tg03Fbj16Tg03GXj19Tg03HMj1;Tg03IDl98Tg02P0j5RTg01>Sj1QTg01K6j1PTg00BMj27Tg01Kmj2OTg01LMj1NTg0379l=KTg03JCl9CTg035cj2BTg03K;j1DTg030Hj2ETg00Iej1FTg00`Mj3GTg009hj3HTg02lFj3ITg00CEj2JTg02Vkj3>Tg03Koj3LTg03Llj4MTg03Mdj5=Tg00D>#0#0#0R0#0#0#0#<#:R1f1R2#?=212g03N]#1g00Bgg03O\g03P\g00C`g03Q\%<0#:#1#1f=R0f<R3f:R4#4f6R5f5R6f7R7f3R8f2R9E53A%@9P3f?R:P8P9P3f;R;P4f9R<P5f4R=#3%6=%9=%;=M98DRP0f@P:f>P=P8P0P3P;P4P7%36%66%96%;6M98%40P<f8R8P4P5P6E5R=%Q1%P='71O11#1%N='7P9P2f0R9M=KP0P3P;P4P<P8P7P5P6M9Cg01XbR=#1R:g02^0fA/B5%D7,E6%F=5G=5H=92:2AI629'JW<WBR95>0eAL03;P5P4P<P8P7CMP6P9D=eW3W0W2X71W5W9W:W?X;1X41XA1W>W=W@W1X61W8o"). Qed.

Lemma wall_obs_iff : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit segs fd bufs code (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]).
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h01oh12trh21Hh33Hbmh43Heqh55Hfd32h64Hfdch72Hwh82Hxh94brk0h:4bufsh;2chh<4codeh=2fdh>3inph?3limh@2mbhA2pchB2phhC3rndhD4segshE2sphF3tr'p;1p;3p;6p;9p;5p;2p;Ap;4g00?Mj14Tg00@2j1=Tg00=Bj1<Tg00ATj1ATg00=ej30Tg00F;j17Tg03D5j1FTg03E3j6DTg01MEj3CTg032Cj1BTg03Elj1@Tg03Fbj1?Tg03GXj1>Tg03HMj1QTg03IDl9PTg02P0j5OTg03JCl9GTg035cj23Tg03K;j15Tg030Hj22Tg00Iej1ETg02lFj38Tg00CER0j29Tg03RVj1:Tg01[nj1;Tg03SOlAHTg03A9j4ITg01G7j4JTg02ZIj6KTg03TLj5LTg00`Mj3MTg009hj3NTg01XbR1f1R2f0R33Mp=1AN123p=6g00D>#4#4#4R4#4#4#4#=#<R5%A2=052g03N]#7g00Bgg03O\g03P\g00C`g03Q\%=4#<#7#7f=R4f<R6f:R7#Ff6R8f5R9f7R:f3R;f2R<ED3C%B<P6f?R=P;P<P6f;R>P7f9R?P8f4R@#@%?@%>@%Q@M9PDO%71RAf>RBPBP4P6P>P7P?f8RCP:P8M9GRDf@RE/39%58,2@%E1R1'1'6PBPDg02^0RDfB/3:%5C,28/11'690A2RFA8823'9W0X1A%:3#;,9FX0DX1AfAPEP=PBP4P6P>P7P?PCP:P8P9P@P;P<P2MAHfD/3?%57,2C/11'6RB90A2A8C23'9X0DX1AP2P3O2P0fC/3C%5?,2:/11'690A<A8:<2A0A;B%:<#;'9P3fE/37%5>,2?/11'690A@A879@fG/36%54,2>/11'690A8%:9#;P2P>P8P9P3CICJW8W4P2P3O2n2001000000120000000W2X0DXFAEKP3DLW1W7W3W6X<5W:W>W?WCX@5X95XE5WBWAWDW5X;5W=o"). Qed.

Lemma wall_no_error_run : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit segs fd bufs code (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h01oh12trh21Hh33Hbmh45Hfd32h54Hfdch62Hwh72Hxh82_Hh94brk0h:4bufsh;2chh<4codeh=2fdh>3inph?3limh@2mbhA2pchB2phhC3rndhD4segshE2spp;1p;3p;6p;9p;5p;2p;Ap;4g00?Mj10Tg00@2j1;Tg00=Bj19Tg00ATj1?Tg00=ej31Tg00F;j17Tg03D5j1DTg03E3j6BTg01MEj3ATg032Cj1@Tg03Elj1>Tg03Fbj1=Tg03GXj1<Tg03HMj1MTg03IDl9LTg02P0j5KTg03JCl9ETg035cj23Tg03K;j16Tg030Hj24Tg00Iej1CTg00`Mj35Tg009hj38Tg02lFj32Tg00CER0j2:Tg03SOlAFTg03@<R1j2GTg03A9j4HTg02ZIj6ITg03BAj3JTg00D>#0#0#0R2#0#0#0#;#9R3f1R4#?=134g03N]#7g00Bgg03O\g03P\g00C`g03Q\%;2#9#7#7f=R2f<R5f:R6#Df6R7f5R8f7R9f3R:f2R;EB3A%@;P5f?R<P:P;P5f;R=P6f9R>P7f4R?#>%=?%<?%M?M9LDKP2P5P=P6P>f8R@P9P7P8M9ERAP2PAg01XbRA#7RBg02^0RCfA/37%69,48%CARD55A58A91B4f0RE9284':W0W1P1f@P<f>P2P5P=P6P>P@P9P7P8P?P:P;P4PEMAFfC/3@%6>,49=5AD58A91B4A294E':X0CX1BP4PEO2P0fB/39%6@,47=5AD58A91B;A27;41G:;PEfD/3>%66,4@=5AD58A91B?A2>8?P6P7P8PECHW7W8P4PEO2n2001000000120000000W2X0CX1BEI5J2W6W3W5X<3W:W>W?WCX@3X93XE3WBWAWDW4X;3W=o"). Qed.

(* [comment removed for export] *)
Lemma wall_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
  to_wallexit source_segs (Z_to_bv 64 1) bufs code
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  to_wallexit target_segs (Z_to_bv 64 1) bufs code
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  bufs_modeled bufs ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h03inph12trh21Hh31oh42enh53en1h63en2h73imgh84img1h94img2h:5lemmah;3limh<4lim1h=4lim2h>3Hbmh?4HfdSh@4HfdThA7HsourcehB7HtargethC2HxhD2_HhE4abrkhF3ambhG3apchH3aphhI4arndhJ3asphK4bufshL4codehM4rbrkhN3rmbhO3rpchP3rphhQ4rrndhR3rsphS;source_segshT;target_segsp;1p;2p;9p;5p;6p;3p;4p;7p;Ap;Bg00F;j1@Tg00?Mj14Tg00@2j1MTg00=Bj1GTg00@Pj1rTg00@nj2bTg03Elj1ITg03Fbj1PTg03GXj1LTg03HMj1KTg03IDl9HTg02P0j5QTg032Cj1YTg01>Sj1qTg03D5j1XTg03E3j6UTg03UIj1TTg03V=j2STg03W5j1`Tg01QSj2_Tg00=ej31Tg03Wmj1]Tg00BMj2OTg01G7j4;Tg01MEj3NTg03Koj33Tg03Llj45Tg03Xgj1\Tg03Yij1Jj3nTg03Zaj56Tg03[\j7[Tg03JCl97Tg035cj2:Tg03K;j18Tg030Hj2ATg00Iej1ZTg00`Mj39Tg009hj3=Tg02lFj3>Tg00CER0j2BTg03SOlApTg03\ej4oTg03A9j4jTg03]aj4iTg03^fj6hTg03Mdj5eTg03_dj7<Tg03a3j40Tg03acj12j2RTg03bYj2DTg03c_j7aTg03e2j3?Tg00fAj3VTg03ehR1j2ETg029Ij2cTg03fAl9dTg03g;lBWTg02X\j3^Tg02YNj7fTg03h7j4gTg03hej1CTg01[nj1FTg03i[j4kTg03jYlAlTg03kZj3mTg03N]#@R2g00BgR3g03O\R4g00D>R5#4#4#4R6#4#4#4#MR7#GR8g03P\R9%M6#G#@#@g03Q\R6f@R:%r5,b7R7f2R5f1R;P:f?R<f>R=f=R>f:R?f0R@#I%P@%L@%K@M9HDQP?P7f3RAP5P?f9RBf8RCf7RDf4RE%I;%P;%L;%K;M9HDQ%YEg03l4RF#qRGfCRH#XP<P=P:g03llRIPAEURJ#T/S7%`7,_FRF31g00YQRK%]7g03mmRL31RM1OGFRN1OKLRLC;AN77J%X>PBPCP?g03nMRJPEEURK#T/S7=1GFPMPNPLC;AN77KfERKfDRL;3HRNPIfBRMfARFP:P<C5RGf5RO%\N#JD6RPPNPIPGf<RQ93=>RRPJf;RSP?PBPCC5RTPOF[PKPKPLPHPMPFP:P<PIPOM97RUg01XbRV#@RWg02^0RX1:7B%8D,AC%ZVRY59V5=VRZ91W;A>C;@'BW3W1R[%JKPKPUP[P7P7g03oNR[PKPLPHPMPFP:P<PIPOPDf6RUP;P5PEMApCo1:7S%8B,A?=9VY5=V91W;A>?;@'BX3XX1WP;P@O2P01:7?%8C,AB=9VY5=VR\91W5A>B5;fI?nA5P@1:7Q%8?,AS=9VY5=V91WEA>QOEfLPUPOP>PUPOP@CjCiWCWDP;P@O2n2001000000120000000W2X3XX1WEhPPePNPIPGPOg040DDePNPIPGPRPJPTPOF<RGPRPJPTPOg03@<RTD6RR'BPGPRg041;RRg00C`RGg0428RNP0PUPOPEP@C0#2PAP5P;P@C0RP#2'DPDPUPOPEPAP5P;F<[RXPUPOPEPAP5P;P@F<PDPUPOP;C0#2PEPAP5P;C0RY#2'DR][PCPDPUPOPEPAP5F<\]PUPOPEPAP5P;P@FaP;n2001000000120000000X06X6NX=GX9RW5W<W8PX^06^6N^=G^9R^5N^<G^8RP@fFRX?3KLR]PIPHPMPFP:C5R^A3<=>R_PJPQPSP?PBC5R`PUfGRaPaPXPKPLPHPMPFPIPDM97;?@AVV@ZRZ'Ep-0RbP1g0430fHRcPcPaPXPKPLPHPMPIPCM97;?;AVV;\R\P@PFP:P<P=P>PQPSPJPCM97=?F;RVPV1cbVM9dW:P7P7P[PaPXPKPLPHPMPFPIPDPBPCPAPEPUP@MBWP:P<P=P>PQPSP?PJPDM97=?:@/EZPbP1g043a9^b1P\PVP\P@FfW:P7P7P[P:P<P=P>PQPSP?PJPDPBPCP5PEPOP@MBWPbP1g044SPZCgO2O2A3aXKPIPLPHPMPFC5PDC0/R@A3:<=PJP>PQPSP?C5PDC0/R@'EeX1WP]PIP^PUC0#2P_PJP`PUC0R^#2'DeO8b2P0%CP#FPEPAP5P;PTD6[RPPAP5P;P@PTD6%CY#FRY[POPEPAP5PTD6\YPAP5P;P@CkP;n2001000000120000000X06X4NX;GX7RPP^06^4N^;G^7RP@P_PJP`PUP7P7P[P<P=P>PQPSP?PBPJPUPCPDP;PAPEMAl%C^#FeO5b2C;3mC;b@b?W>WBWAW0XL8WKXI9XF8XE8XJ8XH4XG3XT2WQXN8XM8WRWPWOWSo"). Qed.

(* [comment removed for export] *)
Lemma wall_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
  to_wallexit source_segs (Z_to_bv 64 1) bufs code
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  to_wallexit target_segs (Z_to_bv 64 1) bufs code
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  bufs_modeled bufs ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
ltac2:(KReplay.run1 (kr_t_WallSim ()) ["WithFP1"] "h05lemmah13Hbmh24HfdSh34HfdTh47Hsourceh57Htargeth64abrkh74alimh83ambh93apch:3aphh;4arndh<3asph=4bufsh>4codeh?3inph@4rbrkhA4rlimhB3rmbhC3rpchD3rphhE4rrndhF3rsphG;source_segshH;target_segshI2trp;1p;2p;9p;5p;6p;3p;4p;Ap;:p;Bp;7g00F;j16Tg00?Mj10Tg00@2j1ITg00=Bj1LTg00@Pj1gTg00@nj2aTg03Elj1DTg03Fbj1@Tg03GXj1>Tg03HMj1=Tg03IDl9<Tg02P0j5:Tg032Cj1STg01>Sj1fTg03D5j1NTg03E3j6FTg03UIj1HTg03V=j2OTg03W5j1]Tg01QSj2\Tg00=ej38Tg03Wmj1[Tg00BMj2?Tg01G7j44Tg01MEj3ETg03Koj35Tg03Llj42Tg03a3j41Tg045Cj1ZTg046Ej2YTg03jYlAJTg047El:XTg048Hj1WTg03acj1Mj2ATg03bYj2VTg03hej1UTg01[nj1TTg00CEj2RTg03JCl97Tg03e2j33Tg035cj2QTg03K;j1PTg030Hj2BTg00Iej1eTg00`Mj3;Tg009hj3CTg00fAj3KTg03ehR0j29Tg029Ij2dTg03fAl9`Tg03g;lBGTg02X\j3_Tg02YNj7^Tg03h7j4bTg03kZj3cTg03N]#6R1g00BgR2g03O\R3g00D>R4#0#0#0R5#0#0#0#IR6#LR7g03P\R8g00C`R9%I5#L#6#6g03Q\fBR5%g4,a6R6f2R4f1R:P5fAR;f@R<f?R=f<R>f0R?#D%@?%>?%=?M9<D:f;R@P6f3RAP4P@f:RBf9RCf8RDf5RE%D:%@:%>:%=:M9<D:f4RF#Sg03l4RG#fRHfERI#NP;P<P5f>RJPAEFRK#H/O6%]6,\GRG38g00YQRL%[6g03mmRM38RN1?HGRO1?LMRMC4AE66K%NJPBPCP@f7RKPFEFRL#H/O6=8HGPNPOPMC4AE66LfGRLfFRM;5IP<fDROfCRNP5P;C2PEC1RG#Zf=RH95=JPDP>P@PBPCC2PEC1RP,YGPLPMPIPOPNP5P;P<PEP6P6g03oNRQPLPMPIPOPNP5P;P<PEPKf6RRP:P4PFMAJM:X%WG%MG%MP'VRG%UP#TRP'RPGPPg01XbRS#6fHRTPTPLPMPIPOPNP5P;PRM97;3?1Q6D%PR,BK%eSRU5;S5CS9KS?RV'9p-0RWP0g0430fIRXPXPTPLPMPIPOPNP5PKM97;3:1Q6C%PK,BD=;SU5CS9KS:RSP?P;P<P=PJPHP>P@PBPKM97=3;:RUPU1dWUM9`W0P6P6PQPTPLPMPIPOPNP5P;PRPDPKP4PAPEP?MBGP<P=PJPHP>P@PBPCPRM97=3<?/9VPWP0g043a9_W0PSPUPSP?F^W0P6P6PQP<P=PJPHP>P@PBPCPRPDPKP:PAPFP?MBGPWP0g044SPVCbO2O2A5TLMP;PIPOPNP5C2PRC1/A?A5<=JPCPHP>P@PBC2PRC1/A?'9eWIPGeP6P6PQP=PJPHP>P@PBPCPDPEPKPRP?P4PAMAJPPeC43cC4b3b2W1W5W4W?X>7W=X79X;8X87X67X<7X:3X92XH1WAWEXB7X@7WFWDWCWGo"). Qed.
End WithFP1.
