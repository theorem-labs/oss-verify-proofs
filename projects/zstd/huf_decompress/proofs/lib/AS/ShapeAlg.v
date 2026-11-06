(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import SimInv ExitSim CatSim MmapSim AllocSim WallSim.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ShapeAlg () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List:fold_rightC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init6Specif9proj1_sigC47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC47Corelib7Classes9MorphismsBpointwise_relationC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC47Corelib7Classes;EquivalenceEpointwise_equivalenceC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List:Proper_mapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00c59OSSVerify5KrLib2AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C47Corelib4Init5Logic3iffC47Corelib4Init5Logic7and_indc59OSSVerify5KrLib2AS8ShapeAlg8wr_indexC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg5t_altC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg?is_prefix_nil_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvc59OSSVerify5KrLib2AS8ShapeAlg=t_writes_pickC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg:t_write_chC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics?LinuxProcessSem5State5event02c59OSSVerify5KrLib2AS8ShapeAlg8t_writesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg;t_writes_chC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03c59OSSVerify5KrLib2AS8ShapeAlg>t_emit_has_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg5t_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib2AS6CatSim:wevents_chC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg?is_prefix_app_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgCis_prefix_app_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib2AS8ShapeAlg@t_writes_ch_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim7weventsC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc59OSSVerify5KrLib2AS8ShapeAlgDt_writes_ch_exit_iffC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityC59OSSVerify5KrLib2AS7WallSim>wevents_ch_fd1C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses=iff_ReflexiveK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef6firstnC47Corelib4Init9Datatypes6lengthK47Corelib4Init6Specif3sig01C47Corelib5Lists7ListDef5skipnC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClassesEEquivalence_ReflexiveC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib5Lists4List<firstn_skipnC46Stdlib5Lists4List7map_appc59OSSVerify5KrLib2AS8ShapeAlg7wr_fullC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_allC56Stdlib5Arith8PeanoNat3Nat7le_reflC46Stdlib5Lists4List9skipn_allI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init6Specif3sig00C47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_ReflexiveI47Corelib5Lists7ListDef6Forall00I59OSSVerify5KrLib2AS6CatSim5wpick00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim5wpick01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim=wpick_weventsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim5wpick02C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef:Forall_indc59OSSVerify5KrLib2AS8ShapeAlgIt_writes_ch_pick_exit_iffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg8pnode_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Cfg?cfg_transparentC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00C59OSSVerify5KrLib3Lib3Cfg<sstep_of_cfgC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib2AS7ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib3Cfg@alloc_no_b_falseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3CfgDtransparent_nonallocC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics?LinuxProcessSem3RunAalloc_mark_sysnosI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02k59OSSVerify5KrLib2AS8ShapeAlg8realizes01C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02c59OSSVerify5KrLib2AS8ShapeAlg<realizes_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3CfgCstar_cfg_halted_nilC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg00C59OSSVerify5KrLib3Lib3Cfg<star_cfg_oneC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg02C59OSSVerify5KrLib3Lib3CfgAobs_trace_cfg_nilC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=obs_trace_cfgc59OSSVerify5KrLib2AS8ShapeAlgBrealizes_star_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg@realizes_pclosedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg?realizes_admitsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsK4ELinuxProcessSemantics?LinuxProcessSem5State5event04K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00C59OSSVerify5KrLib3Lib3CfgEsstep_cfg_halted_noneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg7rz_pathC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg=realizes_stepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<star_cfg_indC4ELinuxProcessSemantics?LinuxProcessSem3RunAreaches_error_cfgc59OSSVerify5KrLib2AS8ShapeAlg<rz_path_starC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgCrealizes_no_sserrorC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib2AS8ShapeAlg:t_alt_unitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgArealizes_nonemptyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg:t_eq_transC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS8ShapeAlg8realizes03C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00K47Corelib4Init9Datatypes3sum01K47Corelib4Init9Datatypes3sum02c59OSSVerify5KrLib2AS8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC59OSSVerify5KrLib3Lib3CfgAtransparent_instrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01C59OSSVerify5KrLib2AS7ExitSim?sstep_instr_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg:node_instrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg:rz_silent1C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg7rz_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim:msteps_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim7fd1chanC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC59OSSVerify5KrLib2AS6CatSim;buf_modeledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3CfgGtransparent_nonalloc_noC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC59OSSVerify5KrLib2AS6CatSim;write1_ok_nC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateRmaterialize_model_accesses_no_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C59OSSVerify5KrLib2AS6CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim?sstep_write_invC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00c59OSSVerify5KrLib2AS8ShapeAlg;node_write1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedc59OSSVerify5KrLib2AS8ShapeAlgCtransparent_exit_noC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC59OSSVerify5KrLib2AS7ExitSimBin_sysno_sys_inputC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7ExitSim@exit_dispatch_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_killed_with_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep06C59OSSVerify5KrLib2AS7ExitSim>sstep_exit_invC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS8ShapeAlg8realizes02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg8rz_emit1C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andK47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib2AS7MmapSim>munmap_args_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim:munmap_effC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim<munmap_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim9munmap_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSimCmunmap_model_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSimDmunmap_model_no_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim@sstep_munmap_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim=page_round_upC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim8to_wexit00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim<bufs_modeledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg7rz_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgAt_writes_pick_nilC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffc59OSSVerify5KrLib2AS8ShapeAlg9rz_write1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgBt_writes_pick_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim<to_wexit_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib2AS8ShapeAlgEexitline_realizes_auxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7WallSim7to_wall10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSimAbuf_modeled_skipnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg:t_alt_wallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg8t_eq_symC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7WallSim7to_wall00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7WallSim>to_wall_mutindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7WallSim;to_wallexitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgAexitline_realizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg<rz_wall1_mutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgHt_writes_ch_exit_has_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg=t_writes_consC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7MmapSim3twm10C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7MmapSim3twm00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSimDmunmap_model_fd1chanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim?munmap_model_fsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg9rz_munmapC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7MmapSim3twm20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim:twm_mutindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg@twm_realizes_mutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg@t_writes_ch_pickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim6fdchanC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32C59OSSVerify5KrLib2AS6CatSim=write_ch_ok_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSimBsstep_write_ch_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg=node_write_chC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim;to_wexit_ch00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlg;rz_write_chC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8ShapeAlgEt_writes_ch_pick_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim?to_wexit_ch_indC1?~~~~~~~~~~~~~~~".

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

Lemma is_prefix_app_r {A} : forall (l m a : list A),
  is_prefix a l -> is_prefix a (l ++ m).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "p'0h01Hh11ai001ah21mh31li011lh41Ah51yh62H0h72IHh82a0h91xp;1p;3p;2p;4p;6p;5p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0g002QR5p4p710R6p9P0p1002op4p710R7p9P0p1003gp4p710R8p9P0g004FR0p4p710R9p8p1004cp4p70R:p1005Sp4p710R;p8P:p1005op4p710R<p8P:p1006Mp4p7210R=p8P:p1006jp4p710R>p8P:P6p8P:p1007Jp4p7210R:p8p200R?g007gR@p4p710RAp8P?g008]RBp4p710RCp8P?P6p8P?g009WRDp4p710p8P?P9p8p100:9p4p710REP;p8PEP6p8p100:Vp4p70RFP1p8PFP2p8PFp100;Dp4p7210p8PFP;p8PFPAp8PFP?p8PFp100;`p4p7210p8PFPEp8PFP<p8PFp100<Op4p710p8PFP=p8PFPCp8PFp100=Jp4p710p8PFP4p8PFP3p4p710p8PFP>p8PFP6p8PFp100>Fp4p7210p8PFP7p8PFP:p8PFP9p8PFp100?:p4p7210R9p8PFp100?Wp4p7210p8PFP8p8p100@6p4p7210R8P;p8P8P<p8P8P=p8P8P6p8p100@bp4p70R8P;p8P8P<p8P8P=p8P8P>p8P8P6p8P8P:p8P9P;p8P9P6p8p100AXp4p710P6p8g00B7R6j13TP@j30Tg00BWj14TP0j37TPBj2<Tg00C7j31Tg00CWj2;Tg00D6j35Tg00DPRBj26Tg00Dkj28Tg00EEj49TP5j6:TPDj5=Tf4RDf3R5f2R0f1R@f0R93730p=2%39P@%3@R;%30R:%35R8A0D90f5R>P@P>P5P0D2[]1]2W3%459059P6PD%4>R=90>9f6R<P@P<%4<PDD2]0P@%4DRF=0DFA7>=5,<>W0f7R=#3f8RFA1F@9%4FR730f9R3A130@P3%43P=D2/;9W0W8X1<P@P9O2n10110100020020100101P9O1W0X1:X2;%3DR;A0>90P<P@P<P5P0D2[]1^28%3>A1<D590<9P6P=A1F<>R690F9P3P@P3A13=<PDD2]0P@%4=A1=>D50=g00E`PFP7PFP6P5D2eW0f:R6#3f;R7A17@9A173F30PBf<RB?506A0B@3f=R8?557P8P0P8P6PFD2'6P9f>RF?5DBf?R5P8f@R4?0>8fARC?5@5PCP<PCPFPBD2'6[X55A05DBA54FFP4P>P4P8P7D2184FPBP7P>P9O3C9W0P>P9E:W6P@P9O2n2001000000120000000PBA1B0@PBA1B63P=D2eW0W1X53P@P9O2n10110100020020100101P9O1W0W1X2;W7X3:X9@P9D=W3X4?P9O1X4?o"). Qed.

Lemma is_prefix_app_split {A} : forall (l a b : list A),
  is_prefix b (l ++ a) ->
  is_prefix b l \/ exists b', b = l ++ b' /\ is_prefix b' a.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "p'0h02b'h11Hh21bh32H0h41ai001ah51li011lh61Ah72Hph81yh92IHh:1oh;1xi021xp;1p;3p;2p;4p;7p;6p;5p200R0g007gR1p4p710p8P0g002QR2p4p710p8P0g009WR3p4p710p8P0g004FR4p4p710p8p100:Vp4p70P0p8g00B7R5j11TP1j32Tg00BWj19Tg00F<R1j28TP4j36Tg00D6j37Tg00Dkj2=Tg00EEj4<Tg00FVj4?Tg00G0j3>Tg00C7j30Tg00GJj3BTP2j7Fj6ETP3j5DTg00DPR3j2@Tg00GdR2j2CTf4R4f3R6f2R7f1R8f0R93632p=4f5R:A6678774/@9p=3A24671889'Cp=5A0678=649p=;A7:46A2789'@p=:A67899746p=A%19P8%18R;%17R<%16R=P4P9P4P7P8D4P:P8P6%1:R>f6R?#1R@P7P?P4P9A2?96E3X0>D5[]2]4W5P6P9P6%96P8D4%94RA9248%14RBP>P7P:%9:P9A2:96E3X0BRC'8PBPCP8A64A8RA97B8A24871=BAP9C<C?3>W1X2<X4;P:P9P:P7P8D4P?P8P6P@f7R;#1P7P;P4P9A2;96E3X0@D5[^2B^4=P?P9P?A0?46P8D4P5P;f8R5P9P5A05?:R=P6D4f9R@P8A0@;?RA%1@RCf:RD#1REP7PDPDP5P;P9D;PDP9P:E:X0CD5]1P8P;%9;P;A0;:4P7D4%95=25=%15R=PC%9@P@PAP9A2@94E3X0='8g00E`3BW1f;R=A0=89P=A0=@5P?D4P3f<RA?77DPAP8PAP@P;D4f=RCA0C67A0C=D%1CRFf>RG#1A0G46PGPGPAP=P9D;PGP9P@E:X0FD5P9A7G4Af?RFPCf@RHP:PHPCP=D4fARIA0I8?A0IFG%1IRJfBRK#1RLA0K7;PKA0KHFRMP9A2K9CRNE3X0JD5[X8FPFP4PFPAPDD4PAP=P:P9O3PHP:PC%1HROPJP?PIPGP9A2I9AE3X0OD5P2A2I?GPLP;PKPFP9PNE3X0J,8JPKA0KH;PMPLfCRM#1RJA0MI5RNPMA0MIHR2P9A2M9GROE3X0LD5P9A2K;FA2MN2R2fDRN#1RPA0NK@RQPNA0NKIRRP9A2N9FRSE3X0J,8JA7MIIA2M5H1=MIP9C<P2e3BW7P9O1PJP5PMPHP9POE3X0L,8LP1PJPPP@PNPIP9PSE3X0JPNPQPRPPfERR#1RQA0RMDPRPRPMPKP9D;PRP9PHE:X0PD5P9fFRP#1P=PPPMP9A2P9IE3P3fGR3#1PAP3PNP8DAA238KfHRKA0KPCA0KPR%1KRCfIRA#1RIA0A3GPAPAP3PPP9D;PAP9PNE:X0CD5P9PIPGPAPPP6DAfJRG#1RIA6G34R4fKRCP9PCPKPPD4fLRN?2?3RMfMR=A0=C7A0=CGR7%1=RHfNRJ#1A0JN6PJPJPNPCP9D;PJP9PAE:X0HD5[]1X2IPGP4PGP3PRD4A2C:PA6NA?90NGRPA0NGARA52N%1NRRPHA6=G;90=CP=P7P9A2=9KE3X0RR='8PRP=P?A6NA?RA97RPPM1=RAP9C<C?3>W7W1PFP9PDFFW3P8P9O2n2001000000120000000W3X0QP8P9O2n2001000000121102000W3P9O1n200100000021000011000b:W1P:P9EEW3P8P9O2n2001000000121000000W1X2EX8@P8P9O2n10110100020021100101P9O1W1X2>X4BW9X5<X;8P9DDW5X60P9O1X60o"). Qed.

Lemma is_prefix_nil_r {A} : forall (a : list A), is_prefix a [] -> a = [].
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "p'0h01Ah11ai001ah22a0i011lp;1p;3p;2p200R0g007gR1p4p710p8p100:Vp4p70P0p8g00B7R2j10Tg00BWj11TP1j33Tg00D6j32Tg00Dkj26Tg00C7j34Tg00CWj25Tf0R1#0P2f1R2f2R3%13R4731f3R5#0%15722[P1g00H>%03R6/64U%12R7=327A2644[ef4#0g00HZf6R6#0A4632%1632R6/51Uf5R3A4321%1333P6[eW2X15P2P1O2n10110100020020100101W1X00P1O1X00o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TSet := list event -> Prop.

Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.

Lemma t_eq_refl : forall T, t_eq T T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Hh11Th22trp;1p;4p;2g00B7j12Tg00EEj41Tg00I7j20Tg00Ilg00Ja#2f1R0f0R1O1R2f2P0O1[R0P0P1X02R2P2C1W21011eW1o"). Qed.
Lemma t_eq_sym : forall T T', t_eq T T' -> t_eq T' T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h02H1h12H2h22H0h31Hh41Th52T'h62trp;2p;1p;5p;4g00I7j21Tg00B7j14Tg00KWj22Tg00L0j50Tg00EEj43Tg00IlR0f1R1f0R2'1g00Ja#4f2R3P2O1R4f4R5P1O1R6[f3R7P2O1R8P7P1O1R9[1269R9f5R6P3O1R:P6P7O1R6[R;P5P3O1R<f6R=P7O1[R>P:f7P5O1R:\6R6P2X1:P2P7O1O1W1X0;P2D0W0P3P1O1R:O1X24P;P>P<P=P5O1P2W0P1P7O1O1X16X0;P2D0X09P:O1X28C3W61113eW3X50W4o"). Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h02H2h12H4h22H5h32H3h42H1h51Hh62H0h72T1h82T2h92T3h:2trp;2p;1p;5p;4g00I7j22Tg00B7j14Tg00KWj21Tg00L0j50Tg00EEj43Tg00IlR0f2R1f1R2'2R3g00Ja#4f5R4f0R5O1R6f4R7P2O1R8[f3R9P5O1R:f6R;P2O1R<[P4P2O1/18R8P;P1O1P;P9O1R=[R>P4P1O1R?f7R@P9O1[RAP?f8R?P7O1RB\=R=f9RCP7O1/1Bf:RDP4O1PDP;O1RD[REPCP4O1f;RFP;O1RG[P?P4O1R4f<RHP@O1RI\DPFP@O1RFf=P?O1RJPHPCO1P5W0P<O1W2P2P5O1O1W1P2P;O1O1W2X1EP5D0W1P;P7O1O1W3X0>P5D0W0P1P2O1R2O1X46P>PAP@P1O111GDPHP?O1RH\IRGPJ\FPIf>PCO1RC\HP5X2CP5P7O1O1W2X1GP5D0W1P?P;O1O1X04P1P5O1O1X3BP5P9O1O1X3=X0>P5D0X08P2O1X4:C3W:1271eX63W5X90X80W7o"). Qed.

(* [comment removed for export] *)
Definition t_nil : TSet := fun tr => tr = [].

(* [comment removed for export] *)
Definition t_emit (evs : list event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.

(* [comment removed for export] *)
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.

(* [comment removed for export] *)
Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.

(* [comment removed for export] *)
Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
  t_emit [ExitEv code fs] t_nil.

(* [comment removed for export] *)
Definition wr_index (buf : list byte) : Type :=
  {n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.

Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
    : wr_index buf :=
  exist _ (length buf) (conj Hnb (Nat.le_refl _)).

(* [comment removed for export] *)
Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet :=
  t_alt (fun i : wr_index buf =>
           t_emit (map (WriteEv ch) (firstn (proj1_sig i) buf)) T).

(* [comment removed for export] *)
Definition t_writes_pick (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch (Z_to_bv 64 1)) T bufs.

(* [comment removed for export] *)
Lemma t_emit_nil_eq : forall T, T [] -> t_eq (t_emit [] T) T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "p'0h03tr'h11Hh22trh32HTh42Hph52H0h61Th71xi001xp;1p;3p;2p;6p;4p100LMp4p711p100MFp4p710p8g00B7j1ATg00BWj1@Tg007gj33Tg004Fj32Tg00D6j30Tg00DPR0j21Tg00F<R1j24Tg00GdR2j26Tg00N<j39Tg002Qj65Tg00Dkj28Tg00EEj47Tg00FVj4:Tg00G0j3?Tg00O<j3>j2;Tg00KWj2<Tg00I7j2=Tg00JaR3#AR4p-0]7f0R5%@3R6O1A3356f1R7A2365R8504f3R9P5O1'1X04,44'6R:P9P7O1R;[f2R<P5O1R=A3376R>A04<8f4R?P5O1'1X04R@,44RA'6[P2P>PAP?P<O1P5A33<6A9395A0496P4P6f7R2P5O1X24f5RBP?P5E5b4W4P5O1A0498PBP5O1'1X04,44P1P4A04?8f6R1P5O1'1X04P1P?O1P5A0418f8R1P5O1'1P0A2367R09042f9R2P7O1f:R8P1O1P5A23699042P4A236?f=PBO1f>P7O1[X24f<P?O1P5W3P8P5E5W1P7P5O2n2001000000120000000W1X04P7P5O2n2001000000120100000W1P5O1n200100000021000010000X1:P4P@P7A0470P;1840P5C7C:9?>AX3=C7A>6<5/<=eX241;67/=7eW5W6o"). Qed.

Lemma t_writes_pick_nil : forall T, t_writes_pick [] T = T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Tp;2g00Dkj20Tg00IlR0f0,00W0o"). Qed.
Lemma t_writes_pick_cons : forall buf bufs T,
  t_writes_pick (buf :: bufs) T = t_write_ch (Z_to_bv 64 1) buf (t_writes_pick bufs T).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Th13bufh24bufsp;1p;2p;3g00P3j10Tg00PXj12Tg00Q6j13Tg00B7j11Tg00QYj18Tg00R7j27Tg00R]j26Tg00S[j34Tg00Dkj25Tg00TVR0#0#0#0R1#2#3#1R2%12g00IlR2%01#0#0#2%80'7f2f1f0'634,52W0W2W1o"). Qed.

(* [comment removed for export] *)

Definition t_writes_ch (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (fun buf acc => t_emit (map (WriteEv ch) buf) acc) T bufs.

Definition t_writes (bufs : list (list byte)) (T : TSet) : TSet :=
  t_writes_ch (Z_to_bv 64 1) bufs T.

Lemma t_writes_nil : forall T, t_writes [] T = T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Tp;2g00Dkj20Tg00IlR0f0,00W0o"). Qed.
Lemma t_writes_cons : forall buf bufs T,
  t_writes (buf :: bufs) T
  = t_emit (map (WriteEv (Z_to_bv 64 1)) buf) (t_writes bufs T).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Th13bufh24bufsp;1p;2p;4g00P3j10Tg00PXj12Tg00Q6j14Tg00B7j11Tg00QYj1:Tg00R7j29Tg00U;j18Tg00;Dj45Tg00V1j26Tg00O<j27Tg00Dkj23Tg00TVR0#0#0#0R1#2#4R2#1R3%13g00IlR3P2g00Ja%01#0#0#2%:0'9#8f2C5f1f0'6'7,33W0W2W1o"). Qed.
Lemma t_writes_ch_cons : forall ch buf bufs T,
  t_writes_ch ch (buf :: bufs) T
  = t_emit (map (WriteEv ch) buf) (t_writes_ch ch bufs T).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Th13bufh24bufsh32chp;1p;4p;3p;2g00P3j10Tg00PXj13Tg00Q6j12Tg00B7j11Tg00U;j18Tg00;Dj47Tg00Vjj36Tg00O<j24Tg00Dkj25Tg00TV#0#0#0R0#0#0#0#3#2%30#2R0#1R1%11g00IlR1P0g00Jaf3R0#8f2C7f1f0560'4,51W0W2W1W3o"). Qed.

(* [comment removed for export] *)
Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Th11eh23tr'p;1p;3p;2g00B7j18Tg00BWj17Tg007gj30Tg004Fj31Tg00D6j36Tg00DPj22Tg00F<j23Tg008]j24Tg00GJj35Tg00JaR0#8R1g00Il%70R2f1R3500f2f0R45109612P3P4O1'2X21,31140335W0W1o"). Qed.

Lemma t_writes_ch_exit_has_nil : forall ch bufs code fs,
  t_writes_ch ch bufs (t_exit code fs) [].
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "p'0h04codeh12fsh23acch31bh42bsh53bufh64bufsh72chi001lp;1p;2p;4p;3p;5g00P3j10Tg00PXj19Tg00Q6j13Tg00B7R0j14Tg00Wfj2=Tg00BWj18Tg00Vjj41Tg00X]j2;Tg00C7j35Tg00YSj26Tg00U;j12Tg00;Dj47Tg00O<j2:Tg003gj5<Tg00TV#0#0#0R1#0#0#0#9#3R2%91#3R1#4R3#4R4P0P3g00:VR0f4f2R5f1R6f0R7'=R8g00JaR9#8R:C1]1^02P71;67=59:g00ZR'6f3R;%83P8P:C1eX10X02P1P9f7R<#2P;C7g00IlR=P3P1P9f9#2P6C7/:7X2=X53P8P5D<'6P<A53;5P8P:C1eX10X02X44X33P6P7O2n10110000020020100100W6W7o"). Qed.

(* [comment removed for export] *)
Lemma t_writes_ch_exit_iff : forall ch bufs code fs tr,
  t_writes_ch ch bufs (t_exit code fs) tr
  <-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code fs]).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "p'0h03tr'h11Hh22trh34codeh42fsh52H0h62b'h74bufsh81lh92Hch:2IHh;3bufh<2chh=1ti001xp;1p;2p;4p;3p;6p;5g00:VR0p4p70g00[HR1p4p710p8g00P3j1CTg00PXj1OTg00Q6j1LTg00B7j1FTg00Wfj2;Tg00Vjj44j3HTg00BWj1NTg00KWj2<Tg00D6j3=Tg00F<R2j21Tg00GdR3j29Tg00<Oj2YTg00\Ij2XTg002Qj6ATg00GJj3MTg00EEj4ITg00O<j2Wj3KTg00C7j3GTg00\gj2DTg00]`j5VTP1j5UTg00^`j5RTg00DPR1j2?Tg00Dkj2QTg00FVj4PTg00G0j3STg00_dj4TTg005Sj6_Tg00`Bj4^Tg009Wj5]Tg00X]j2\Tg004Fj3BTg007gj3JTg00U;j1ZTg00;Dj4[Tg00JaR4f2R5f1R6'\f0R73Gp=3f3R81D56=B475J4p=:AJ467p=0f4R9AB4567=8/?7p=6AB4679=85p=7AB467p=5P5P4%Z6P7C[p=21D56=B47p=>AB4679J45p=8P8P5P6P7C4,?9p=EP9P81;56P7C4p=@g00TV#C#C#CR:#C#C#C#O#LR;%O:#LR:#FR<#FR=P<%F4R>f5R?P81;56R@P7C4P7P?P8%N4RA9356RBC:'<]2^40^3;X7=107BRCP>P6A385ARDP7A=>7ARED6X0>,1>'9RF106DRG[P>P5A398ARHP7PED6X0>,1>RI,9G\CP3PGPI105HRJP7P7X1JP7O1P>P8A3?9ARJP7PED6X0>,1>P2P>P>P9f6RK?3?ARLP7PED6X0>109LP7P>PKf8RMf7RN;3AP7PED6P1P>PNf9RE?3MAROP6C7A=>6Af:RP?3EARQ,0MP7P>PEf;RR?3PAP8C7P>f<RS?3RA/59A=>?Af>RTf=RU;3ARV,06[X2>A=>9AP>PA15V7/0VX0>P>A3USARW107VX8>1Y4W15WA1X4WEAP?P7EAW1PPP7EAW1P6P7O2n2001000000120000000W1X0>P6P7O2n2001000000120100000W1P7O1n200100000021000011000X5FAMGI7X1CCIP9%N<RIP@P7C4RG/<CeP7P9PIPBC:,<GeX2>X40X3;PKP8P@P7C4P7PKP8PBC:'<^2>^40^3;g00IlRGA2:N?RIAHN9@RC'WP7P6O1P6PMAG<K?PDC:'<X=GP>1DN9RG/5B,5IRFA2:MKRX1;85RY9HM?;K61067'<X8>107IP>P6PXP7PMP?PYP7C4D6X0>,1>'9RZA>M?DR[986X[107FRF106XR\P>P5A2:ENR]P7C7R^PEPK1;98R_P7DEX0>,1>R`'9[P3P\P`A>EKHR`985]P7105]R]P4A2:PMRaA>PNJRJP8P7DVW1P7O1P>P8PaP7C7RbPPPN1;?9P7DEX0>,1>P2P>P>P9A2:RERcP7C7RdPRPM1;K?P7DEX0>ReA>RMLRL989cP7P>PKA2:URP7PUPPPMPNP7D@D6RfP1P>PNA2:TSRgP6C7PTPRPEPMP6D@f?Rh=2:URiA>hSQRQ58MP7P>PEf@Rj=2:TRkP8C7P>fARl=2:hRm/59fBRnPhPUPSP?D@fCRo=2:lRpA>ojVRV586[X2>PlPT1;SRRqP9C4P4A2:njRrP?A>nhWRWP1fERsPnP@P7C4fFRt/DoRu=86D[RvP7PsPnPBC:PtPoPYP6C4Rw[fGRxfDRy'DRz=85H\wPlP5P6P7O3P6n2001000000120000000X2>X40X3;Pv^2>^40^3;P7PTPUPKP6O4b1DUW9PPP7EAW1P6P7O2n2001000000121000000W1X0>P6P7O2n2001000000121100000W1P7O1n200100000021000011000X5ZP4PXP[P6P7DR107`,?^X6>,1>,9\P3P]107J,?bX6>,1>108aRa11>e'9P7109cP>P?A2:SPRcP7C7RePSPE1;NKP7DEX0>,1>;M7X1aP7O1107L,?dX6>,1>P2P>P7PSPEA3NKAC:,?eX6>10?cPfX0>,1>'9P7P>PNPgP7P7PTPRPOC:D6P1P>PMPiP6C7106Q10EkP>PPPmP7PlPTPqP7C4D6X0>,1>'9P7P>PPPmP8C7P>15r910?VA2:ynRV,06P>P5A2:soP7PsPnPjPhP7D@D6X0>,1>'9[X2>109W15p?RW/0pP>15VKPVP7PyPlPhPTP7D@D6X0>Rl,1>P>PlP?A=>WWPoPjPTPUP?D@1Q>WP1PtPoP@P7C4A86zDRz[A87uBPxPyPYP6C4[RYfHPsP_P5C4\zPnP5P6P7O3P7n2001000000120000000X2>X40X3;PY^2>^40^3;P7PhPTPKP6O4b5CICP3SW1PRP7EAW5P6P7O2n2001000000121000000W5X0>P6P7O2n2001000000121100000W5P7O1n200100000021000011000b1X1FCIAKIC7RC/<Fe15IG/5BP4PIPGPBCTE_P7PNAG<?9RGPBC:,<CeAHNG@PNP?P9P@C^EAX2>X40X3;W:X7=X;<P7D]W7W<o"). Qed.

Lemma t_writes_exit_iff : forall bufs code fs tr,
  t_writes bufs (t_exit code fs) tr
  <-> is_prefix tr (wevents bufs ++ [ExitEv code fs]).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h04bufsh14codeh22fsh31lh45lemmah52trp;1p;2p;4p;3p;9p;5p;6g00P3j10Tg00PXj1<Tg00Q6j18Tg00B7j13Tg00QYj1FTg00R7j2ETg00Wfj29Tg00Vjj4:Tg00\gj27Tg00X]j26Tg00BWj1=Tg00C7j35Tg004Fj31Tg007gj32Tg00KWR0j24Tg00aCj1;Tg00b9j2DTg00bel9CTg00c_j5BTg00ddj4?Tg00eRj1@Tg002Qj6ATg00V1j3>Tg00TVR1#0#0#0R2#<#8#3#3%02#0#0#<R2#8g00:Vg00JaR3#3R4%F1,E2R2f3R1f2R5f1R6'9R7f0R8C:1721R91656%=3R:553R;5139238'4p-0R<P0g00fPP2f4R=1915P6C:172=1615=53:R:5139236P8%;==13:9236R=P=1D<=M9CW4P2P1P5P6P8DBP4%;1R5A138:9236/4=X34P<P0g00gAA135;9238R3C?P9%@1EAO2A>178/43eW5W2W1W0o"). Qed.

(* [comment removed for export] *)
Lemma t_alt_wall : forall (ch : word) (rest : list byte) (T : TSet),
  T [] -> (1 <= length rest)%nat ->
  t_eq (t_alt (fun i : wr_index rest =>
          t_emit (map (WriteEv ch) (firstn (proj1_sig i) rest))
                 (t_emit (map (WriteEv ch) (skipn (proj1_sig i) rest)) T)))
       (t_emit (map (WriteEv ch) rest) T).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "p'0h03tr'h11Hh21nh31ih41li001lh52Hph62trh72Hih82Hth95lemmah:3tr1h;2HTh<3Hn1h=3Hn2h>3Hnbh?1Th@1ai011ahA2chhB2l2hC4resthD3tr2hE1xi021xi031sp%0p&0p;1p;2p;3p;4p;6p;;p;5g00P3j1KTg00PXj1iTg00Q6j1_Tg00B7j1^Tg00BWj1gTg00h1j1xTg00LMj1ATg00U;j10Tg00hPj2:Tg00hjj32Tg00MFj3Lj2oTg00O<j34j2JTg00iIj2NTg00iij4QTg00EEj4ETg00jEj33Tg00F<R0j2;Tg004Fj3@Tg00D6j3=j1TTg001?j4lTg00jcj4STg007gj1kj3mTg00kJj3jTg00l;j4]Tg00m2j3\Tg00mhk401Tg00b9j2hTg00;`k300Tg00;Dj2~j4BTg00?Wj2}Tg00nUj1|Tg00>Fj4{Tg00oFj3zTg010>j4fTg0111j1wTg011`j6eTg012Kl;PTg013Fj3ZTg00<Oj2vTg00]`j5uTg013gj5[Tg002Qj6?Tg00=Jj6tTg00GJj3YTg00[Hj5sTg00Dkj2WTg005Sj6rTg00_dj4qTg00FVj4OTg00G0j3VTg014Cj2`Tg00DPR1j2ITg015;j2bTg015Zj1cTg016>j2pTg00I7j2nTg006jj3yTf2R2f1R3f0R4'N':p=af3R51N34,:2'Ip=Dg016\R6?y34p=6f5R7g00JaR8f4R9A3523CB/J4p=7P5P8P2P3CB/J4p=MP2P8P3P4CBp=1P9P8P5P2CB?434p=<1:34,I2p=XP9P8P5A2234CBp=HP2P8%03P4CBp=Gf6R:P8P7A2952CB?434p=CAm834p=8A@8239=95/I4p=9A@834p=5P5P8P2P3CB=@84p=>A=523/I4p=RA@8349=52p=FP9P8P5A3234CBp=U1J23=454p=dg00TV#K#K#KR;#K#K#K#i#_%i;#_R;#^R<g00IlP4%g8R=O1g017;#xR>?a;2%^8R?%A9R@P;%0:RA1:>4RBP4P;P:CDX26/64RC=2;7P;PAP;PCP7P9E7CMX3@;L4R@A1;A7RA?493[P;%07RCP9P5P4D<RD%A7REP;f7RF#0RGP;1N;FRH9XB4X26/64RIP:DHRJP;PGP;PIP:P7E7RI'JX3E;L3[P0PEA4JI2X3EA1;G:RG?472P4%AFREg017ZP6PBP4P;f9RICDX26RJP;f:RK#0RLP;PBP4P;PKCDX26/64RMPIDHRNP;PLP;PMPIf8RME7RL;47f;RO=G;KS00?4I:[P4PBP4P;POCDP11:>3f<RP9a3;P;f>RQ#0RRP;PBP4P;PQCDX26RSP6PSP2P4CQ'6RTf=RUP;PRP;PTPUPPE7PIFCf?RT=G;QRV?4UK[P41:>51N;TRW,:9P;fARX#0RYP;PBP4P;PXCDX26RZP6PZP71:>7f@R[,N;R\,:7P3P4CECQ'6R]P[P;PYP;P]P[PTE7PPFCg00GdR]P;fBR^#0R_P;P:PXDH,8UP?PQP;fCR`#0RaP;PFP^DHRbP4P;PaA3;F^PXP4D<D9X0?,;?P;PaP^PXPQD<P418QbfDRb#0Ra=1;`Rc,8TP?P[fERd#0Re=1;bRfP4P`P4O1D9X0?,;?P8PTA2;M`Rg91;aRhPcP4A3;M`Rc9@;gRi==<`P?p-0Rj^B?Rk%T?RlP?PjPlPjPjPjg0186RmClRnCSRo%k8RpPk\?RqP?PkPlPoCSRrP?PkPoP?PjPng018T9jjmC]C]9\qrPpH01S01A2;IbRr91;eRq1h?qPfA3;IbRm9@;rRr91;eP8\;RjP?^4<S02%T8Rn:00;8RsP<P?%T<RtPlCSS031~;8S041};8S05PePjPsP;P8Pn%|8C{9zjs9\jsRnPeCfPbPrP<Pt%w<RuPrPbP4EeM;PM;PW9AZ;M`P?A1;acRr,5h18q4X4?P8PhPrPh1v8hDuA1;aiP;P8PaPgPcD[E?O2Et3YW5P4O1P?PTPhP4A4r^4D9X0?,;?P0P?P?P[PqP4P;PePmP`P4D<D9X0?A4f`[P4P?P^P;fGRf#0RmfFRe92;OP4C>P;PmA3;OePdP4D<CRP1P?P`P;fHRm#0RqP;PPPfDHP3CFP;PqA3;PfPeP3D<P;fIRq#0PmPfPbD<P4P?PdfJRbA2;Qq5G;P5CFP?P;fKRr#0RhA2;TbP9C>fLRcA3;[r5G;Rg?4b7fMRa#0Ri=1;cRv?4r3[X6?P;PhA3;TbPqP9D<P]187gP?P:P;PiP;PXPcDURgP4PrP4O1D9X0?,;?P;PiA2;XcP:C>94vrP418:gfNRg#0RvA2;^aRi51;Rh/5FA1;va'8P?P;fORw#0RxA2;`gRyPMC>RzA1;xgR{P4PaP4O1R|D9X0?,;?A3;^aR}9@;iR~==<aP?PkPlPoPpQ01Pz1h?zP{A3;`gR`9@;yRy91;xPjQ02PsQ03Q04Q05PxPjPsPnPxCfPgPyP<PtPuPyPgP4EeM;PM;PW9AZ;^aP?A1;v}Rg,5h18z4X4?P8PhPFPgP4DsA1;v~P;P8PvPiP}D[E?O23YW5P4O1P?PFPgP4PcP4O1D9X0?,;?P0P?P?PMP;PxP`P4C>P|CRX0?A4{azP4P?PKP;fQR{#0fPRz93;dP4C>PwP4O1CRP1P?POfRRwA3;e{5G;P3CFPzP3O1P;fSRz#0RdPwP{P;PdA2;fwPPC>D<P4P?PUfTRwA3;mz5G;P5CFP?P;fURm#0A3;qwP9C>PwP7O1RwfW#0RqfVRf51;RdP;PqP;PrPfDHR{/5374m[X:?PzP9O1%0fRzA2;bmRa51;R|A3;bmR`91;zRx/57'5RcA1;zmRg'8P?P;PqA3;rfP:C>,5{PdP4PmP4O1D9X0?R{,;?P?P{P715g7Rg9=?cPwP?15|xRw/5715d:Rd9=?4X4?P?A@;a`R{91;z154:==?dX4?P<PmP;PqP4P:C>==?dX4<1W?gP{AZ;bmE?PwP;P8PzPaP`D[ErPcP8P|PxP7CqE?P4CECO3VW8PQP4E?W1P3P4O2n2001000000121000000W1XD?P3P4O2n2001000000121102000W1P4O1n200100000021100011000W7PeP4E?W1P3P4O2n2001000000121000000W1X:?P3P4O2n2001000000121102000W1P4O1n200100000021100011000W7W=W<P3P4O2n2001101000121100100W@X26P3P4O2n2001103000121102101WEP3P4O2n2001000000121102000X1@P]183AP?P2PGP4P7P4O1D9X0?,;?%A:RAP;%0MR]1N;MR@9XB4X26Re/64Rx=2;FP;P]P;PxPFP:E7CMX3A;L2P4182GPEP;%0IRGP;16J4RJPMP;PGP;PJPMPFE7P9FCX3E1`F9REP<PFP;PGP4P;PGP;P@PMDUR@/JFP9D<X4<A1;]FRJ,85P?P9A1;GMP4CFRGA4@F4'IX0?,;?;Y4A2;HF1b;FE?P;P]P;P6PePH1:>H1:HHP9%cHCECQ,6eRHPFP;P]P;PHPFP:E7P5FCeP;P]P;16eEREPFP;P]P;PEPFP:E7P5FCeCOW5P4O1P?P5PJP4P:P4O1D9X0?,;?P0P?PFP4O1,IGX0?%AMRG1JNLX3G;L9P4P?P:Q00P4PIP4O1D9P1P?PFAG;POP3CFPKP3O1%APROP;PR16S4RS=2;UP;PRP;PSPUPPE7CMX3O;LMP4P?PIA1;RUP5CFP?15V9PQP7O1RV%A[RRP;P_PBP4P;P^CDX26/64R^=2;XP;P_P;P^PXP[E7CMX3R;L3[X6?PUP9O1%ATRUP;PYP;16Z4RZP[P;PYP;PZP[PTE7A1;Y[RZ/5:RRFCX3U1`TPRUP<PTA1;Y4RXP;PYP;P\P[DUPTPRCdX4<P<%g;R^PZPXPTPRCdX4<%0[R[=1;TR</57RX/8<P?PRPZP4P;PYP^PTP4D<D9X0?RY,;?P?PYP7A=?XXP;P[P^PQP7D<R^1W?X187=P?P:P=P4PTP4O1D9X0?R:,;?P?P:P715=7R=9=?7PV1W?=P4CECO3VP^eCECO3VA3;WT1p;TE?A2;WT1b;TE?P;P[P;AXB4\X26R\P6P\PW1:>W1:WWPP%cWCECQ'6RWPTP;P[P;PWPTPQE7PXFCeP;P[P;16\UR\PTP;P[P;P\PTPQE7PXFCeCOW8PKP4E?W1P3P4O2n2001000000121000000W1X0?P3P4O2n2001000000121102000W1P4O1n200100000021100011000X1DCEW6%A5RDP;PCPBP4P;P7CDX26/64R4=2;9P;PCP;P4P9P5E7CMX3D'oP;%09P5P2CM'neW>W;W?WCWAo"). Qed.

(* [comment removed for export] *)
Lemma t_writes_ch_pick_exit_iff : forall ch bufs code fs tr,
  Forall (fun b => (1 <= length b)%nat) bufs ->
  (fold_right (t_write_ch ch) (t_exit code fs) bufs tr
   <-> exists full, wpick ch bufs full /\
       is_prefix tr (full ++ [ExitEv code fs])).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "p'0h04fullh11Hh21ni001nh33tr'h41ih52H0h61li011lh72tri022trh82Hph92Hwh:3Hn1h;3Hn2h<3Hw0h=2H1h>2b'h?4bufsi034bufsh@1ehA2H2hB2H3hC4HallhD2HchE3bufi043bufhF3tr0hG2HihH3HnbhI2IHhJ1ai051ahK1bhL4buf'hM5bufs'hN2chhO4codehP2fshQ1xi061xi072l0i081sp%0p&0p;1p;3p;2p;4p;6p;8p;5g00P3j1YTg00PXj1tTg00Q6j1kTg00B7R0j1_Tg00h1k101Tg019Ej3oTg00BWj1jTg00F<R1j20Tg00KWj2XTg00D6j31Tg00GdR2j2cTg019fS00j34Tg01:\j1mTg00EEj4@Tg00FVj4OTg00<Oj2gTg00\Ij2uTg002Qj6NTg00GJj3fTg005Sj8ej6UTg00hPj2=Tg00C7j35Tg00U;j16Tg00hjj3ETg00iIj2[Tg00CWj2sTg00Dkj2^Tg00Wfk300j2KTg00LMj19Tg00iij4]Tg00S[j1Ij4wTg00\gj2~Tg01;Rj3}Tg01<Nj8qTg00]`j5|Tg00=Jj6{Tg00_dj4bTg00X]j2WTg00[Hj5zTg006Mj6nTg00^`j5yTg00DPR3j2PTg00G0j3xTg01=Dj8vTg003gj6lj5iTg004Fj3LTg007gj3QTg00;Dj4VTg006jj3hTg00O<j3pTf2R4f1R5f0R6'['=p=Fg00IlR7f5R8f4R9#If3R:/K4P5P6Elp=Ag00JaR;1W45;56p=2AL;56p=3A49:4AQ;56'Pp=DAL;45919:/P6p=8AQ;:41056'cp=MA489:AL;569Q;4'Pp=<AQ;56p=:AL;569Q;4p=HAL;5691:4p=RAQ;56,P4p=GP:P;P4P5CV=L;6p=dP8P;P9AE:45CV=L;6p=;1[56,=4,P:p=7P7P9%I:1K45P6Dip=>f7R<P;f6R=#6g016\R>?h9:=E84CV?p56p=J1=56,P4p=rP4P;%65P6CVp=ZP9P;P:AE456CVp=CP7P9P:P4P5P6Elp=SA1:45/P6p=aA5;569L;4p=\1W45=5;69L;:9Q;9p=BA5:45=496p=`P7P:P4P5P6Dip=TP<P;P=Ah>9:=E84CV?p56p=?g00TV#Y#Y#YR7#Y#Y#Y#t#kS01%t7#kR7#_R?#_R@Q01g00:V%_;RAg017;$01RB?F76XK?RC=o?:P?PCP?P<P8P9P5P6EAf8RDP4P6P5%j;RE92=8RF,36RGDDX0A,0A'X^7AX?@P6A29:EPAPAP5A289ERHP6A1A6ERID8X3ACMRJPD%j?RKP6P4PGDDX0ARG,0A[P<PKP6P5P6PHE<X0A,0ARL1:5HRHPAP4PFP6PID8X3A,0ARM'c[P2PHPMf9RMPKP6P:P6A2<=ERHE<X0A,0AP61:4FRFPAf:RNPKP6P9P6A2D<EROE<RPX0APEA4MKEAH:EH%mMP6C@COW1P6O1PAP:PHP6PID8X3A,0ARHP1PAPAP9POP6PID8X3Af;ROPKP6P8A2MDERQ,36RRDDX0A,0AP6PAP=A2NMERSP6PID8P3PAP<A2ONERTP5CRA1A5Ef?RUPKP6PMf=RVf<RW;2ERX,36S02DDX0A,0AP6PAPMPXP:CRPAf>RX?2VES03/39A1A8EfCRY?4K6RZfAR[f@R\;2ER],36R^7G4X0A,0A[X7AA1A9EPAPE13]5=GZ^X0A,0AX3APAfBR^PKP6A2\UERZ/3E136ZR_DDX0APEA4[KEA2UXER`/3ERa13E`Rb':%m[PAP`AH6EZX6A1g;`1:`bePa1u;`ENC@COP8P6ENW1PNP6ENW1P5P6O2n2001000000121000000W1X3AP5P6O2n2001000000121106000W1P6O1n200100000021000011000X5JP1PAPG1cFHP6P3A4OK5AH85QP=PSPAPAP<PTP6PID8X3ACMP6A4VK:A2WOERQ9HD9Q00PUA1@4KA1A4MRHPXA2^[ERFPAPAPUA2Y^ERGP6PID8X3ACM[[P5A1@KKRJA1AE=R`A1AEDP6A1AEMRaPAPEPUPGPAPAP\fDRb?2YERZP6PID8X3ACMX6APAPEfERc?4K6AH\5ZP[A2cbERdPAPAP^fFRe?2cEP6PID8X3ACM]8]9X0AA4bKEAHUEG1:\ZPAP[PdP6PID8X3A,0A;f6W8W9PNP5P=P8GePNP6EUb1W5X1JP5P6O2W5W11=B5RJAF479S04fLRd?494A5?=8RG=1@KP7fNRf#6RgAE78<S05P9Cd=1AbA5?D<Rh=1@KP@A5?MDRiP0P?p-0S06P6g00HZRjg00H>S07n10110100020020000000X@@g00E`S08PKP6EUPjP7fQRk#6RlP7PDPNP<E;fGRm51A1=BM1[7WRn,=NfTRo?4WNfORpfSRqfRRr;2ERsPAPAfPRtA2oqERuP6PID8X3ACM]=]5]1]B/s6b1WAP5P6P9P:P4O5WBWAW=W5W1XFAX2>X?@XE?P=P8P9P:P4P5P6O7n10310110700000020171104103100102000000000A1@5KA1A5DS09PVP]PAPAPXPFP6PID8X3ACM[[X6AX6@PKP8O2P61^@K1^A=S0:O2b1W8W9P5P6O2n2001000000121000000X1PX0AP5P6O2n2001000000121106000X1LC@B009:6/XLeP?P=P9P:PKP6EA/XLeX7AAFB75Ao?C5P?PNPDP<P:P6EAPOP9P6P5PRDDX0A,0A'X^7A%98RRP7PWP71=B6RCP6P7P<C7X2>P6P=P?PWPNPMP8D>P5GJX4R'0RRPVA5?<=P6P4P6PTE<X0AS0;,0A[PWPGP6P5P6PSE<X0A,0ARS%9=RTP7PVP7PCP6P7PDC7X2>P6P<P?PVPOPNP=D>P4GJX4TRL'0[P1PTPLPXPhP6P:P6PQE<X0A,0AP6%9Dg017ZP>PCP6P7PNC7X2>P7P\P7PCP6P7POC7X2>P6PNP?P\PXPVPMD>P8GJP^A5?WORQP6P<P_DDX0A,0A[P6ArC6nP3PJ1[7VRn,=5P7PbP7PCP6P7PUC7X2>R_P>P_P4P6C]PXP?PbP^P[PVD>PMGJPeA5?\UR_P6POP6PZE<X0A,0A[P61=B:AF97\P7PmP7PCP6P7P^C7X2>RZP>PZP81=B8AF87[P5P6C@C]P[P?PmPcPbP\D>PWGJP2fHRZAE7=^5Z7,:VPAPXP7fIRL#6S0<P7P<PYDCRTP6P?%ILS0=1KmeS0>P^P6DSD8X3A,0AfJRPA5?bYRIP6PUP6A2ZmERFE<X0A,0AP61:XTPAfKRTA5?cbP6P\P6A2LZEE<X0AP7%6PS0?P7PDPbDCRv1~PYRw'3RxA4PIx13xFRx,:UPPPbPYPDPwP9P:A}PY[GqPA13wFRI,3vRy1:\6X6AP;PUPvPyP6P;PvPIPv1g;vD|E{PxP;PvPwPFCbEUC@COW1P6O1PAPUPvP6P?%IPS0@1KZmS0APYP6DSD8X3A,0AP1PAPAP\P7%6TP7PMPcP6E;P?PTPLPZPbP6EACaX3APdA5?ecP6P[P6A2PLEE<X0A,0AP6PAP^P7fMRv#6P7POPmP6E;P?PvPTPPPeP6EACaP3PAPYP7PgP7PWPZDCP5CRP?PfPdPTPmP5EAPtA5?PLP6PcP6A2fvEE<X0A,0AP6PAPcAE7XP9Z7tP:CRPAP7PlP7PUPTP9E;P?PrPtPpPTP8EAPoA5?fvRlP6P41Wrk=\6ERgDDX0A,0A[X7AP?PkPpPfPPP9EAP3P?PqPkPtPdP6EAfURF?4f6Rw136sRs7G4X0A,0A[RxA4ov6RI?G5gX0A,0AP?PoPrPkPvP5EARy[fVRzPpP6P:136uRuDDX0A,0A\yPLP6O1P5n2001000000120000000X7APx^7AP6P=P5O2AGI<gX0A,0AP1PAAGwDsX0APzA5?tpS0BP6P7%6zP7PbPtPME;PuDDX0A,0AP6fWRuPtP6PNP6A2FoEE<P3fXRs?4k5POP5PzPFPEDBfZRwA5?oqP6P7%6wP7PZPoPVE;P6A2suEE<X0A,0AP6A4wq:PXP9fYRIPsPEDBPAf]RgA5?uzP6P7%6gS0CP7PTPuP\E;RxP6f[Ry?2wEE<X0AP7f\R{#6S0DP7PPPzDCR|/38R}P{P?PzPFP}D`13|UA2wIER~,3}S0E':P{PzPFPPP8PePcP5GqPA138~R},3|1:x6X6AP;P|PUP}P6DzQ0EP;P|P8P~CbEUC@COW8W9P5P6O2n2001000000121000000W1X0AP5P6O2n2001000000121106000bDb1WDPeP6ENW1P5P6O2n2001000000121000000W1X3AP5P6O2n2001000000121106000W1P6O1n200100000021100011000WGW;W:P5P6O2n2001105000121101101WJX2>P5P6O2n2001108000121106105WQP5P6O2n2001000000121106000X1RP1PAQ0;%9<RRP7PXP7PCP6P7PMC7X2>P6PDP?PXPWPOP<D>P:GJX4R'0P6PUPiP6P9Q02DDP3A5?NMRR=4\5Q039H85%9OR~P7P^P7ArC6nX2>P6PWP?P^P\PUPOD>P<GJX4~'0P6A4^Q:AHD9]Q00PbA5?[\R]91@4%9YRQP7Q0?P7PCP6P7PcC7X2>P6PbP?Q0@Q0APYCTPUG?X4Q'0RQ\H[P5A5?XVRH91@KA1@K_P@PKP0P?Q06P6Q07Pjn10110100020020000000X@@Q08P]P6EUPjPQ^5a/s6b5W1P5P6O2X5`W1Q04A4k94A5?dT91@GP7%6qQ05P9Cd=1AbA1@hlP@P@P0P?P@P6PMP6n10110100020020101101X@@PiA5?pfP6EnA1@DfP@P?P0P?P?P6POP5n10110100020020101101X@@PRQ0BP5EnA1?NtA1?OkP6A1?WrP?PqA1@VqRqP7%6yRNP7PVP5PWE;=1Ad1=BXAFU7:f^RR?4[U%9IR0P7f`Ri#6RlP7PCP6P7PyC7X2>P6PwP?PiPRPgPID>PFG?X40'0]<];]:]5[X6?A1@WrP6PqP@PoP7Q0DP7PXPzPVE;=1AvRo1=BURqAF\7sRrf_R0?4:\%9wRhP7faRG#6R`P7PCP6P7P{C7X2>P6PyP?PGP0PRPwD>PzG?X4h'0]<];]:]5X6@P7PNP7PVPFPWE;=1AdP6PoPAP7Q0CP7PUPuPXE;1=B\AF[7IA4iI[%9yRoP7fbRW#6RFP7PCP6P7PgC7X2>P6P{P?PWPiP0PyD>PuG?X4o'0]<];]:X6AA40s\PAP7PlP7P^PwP[E;R[PGP?PyPwP6D`A2i0ERl9Hu5%9gRoP7fdRN#6RhP7PCP6P7P0C7X2>P6PRP?PNPWPGPgD>PIG?X4o'0]8]9X0APiP?PwPIP[D`PzP7P`P7PYPyP^E;P0PRPEDBPAP7PFP7PbP{DCRF/3Y/3l1:s6X6AP613Yl,3FR`P;PFPYPlCbEN1:u`P;fcR;AE7cg5Z7R`1WGi=\bEPsP6DyPsP`PAPAPIP7PhP7PePRDCRhP6P6PcPWPGPEDBD8X>ACMP21:IhPAPwfeRhAE7m05Z7RIP6P6PeP;PWPEDBD8X>A,0A%90ReP7ffR2#6RcP7PCP6P7PGC7X2>R`P6PiP?P2PNP;P0D>RsPyG?X4e'0P61:wI%9iRIP7fgRw#6ReP7PCP6P7PWC7X2>P6PGP?%IwRu1KhNRlPiCTP{G?X4IP>P`PZ1=BZAFZ7iPDP<C@C]RIP7PcP7PZPiDCRF,:yPAP{P7PeP7PLPGDCP6CRRLP?PuPlPiP6DS'PX3A,0A;f6P7PcP7P`PIPiPsPyG?eCOW8P6O1PAPyPFP6P6PmPNP;PEDBD8X>A,0AP1PA1WhN=\ZE9GL6X>A%9GRLP7fhRZP7PCP6P7P;C7X2>P6PWP?PZP2PhPGD>PgGJX4L'0P6PAPRP7fiRR#6P7PTP;P6E;P6PPPwP2PEDBCaP3PAP0fjR0AE7dN5Z7P5CRP5PTPZPwPEDB%9hRTP7flRN#6RPP7PCP6P7PwC7X2>P6P2P?PNP0PRPhD>PGG?X4T'0P6PAPGP7PPP7PfP2DCP:CRPAP7fmR2#6P7PpPwP9E;P8PpPNfkRpPEDB%9RRPP7fpRGP7PCP6P7PpC7X2>P6P0P?%IGRTfnR;/K2RLPRCTP4GJX4P'0[X7AP9PfPpP0PEDB%9ZRPP7foRg#6R1P7PCP6P7P0C7X2>P6PRP?%IgRm1K2NRFPZCTP7P1P7PkPRDCR1/3=RyG?X4PP>PCP6P7PRC7X2>RPPt1=BtAFt7ZP\PUC@C]R\P7%6;RBP7PtPZDCRs/38Ri/:sPAPyP1P6P?PmPFPZP6DSRFD8X3ARm,0APAPmP8A1AiiP?%I;Rm1KNpRpPwP8DS1^AiP3fqR3P0P6P4P6A2g;EE<X0A,0AR1\FA4GR6RG1W;2=\6ERF7G5X0A,0AP?PTPLPRP5DS[RRP?P3PgP;P0P4EA\1PhP6O1P6n2001000000120000000X7APR^7AP6P=PAAGG<FX0APtA4gZtP=PtP2PNPEDBPUP5C@COO2b1C@CO3xP7PBP7PPP\PZP?PmPpPwCTPiG?eCOW8PWP6ENW1P5P6O2n2001000000121000000W1X3AP5P6O2n2001000000121106000W1P6O1n200100000021100011000b8b8W8W9PkP9PvPdGeW<X;rX:qPfP6EUbAW=PXP6ENb=W5PVP6ENb5W1P6O1b5P6O1b5W1P5P6P9P:P4O5W5W1W<W;X:JXFAX2>XM@XL?P=P8P9P:P4P5P6O7n10310110700000020171104103100102000000000A1@5_Q09%9^R_P7Q0<P7PCP6P7PbC7X2>P6PYP?Q0=Q0>P^CTPXG?X4_'0[[X6AX6@PHP8O2P6A5?UX,^@Q0:O2b1W8W9P5P6O2n2001000000121000000W1X0AP5P6O2n2001000000121106000X1SC@POP8P?%IORO1KMDRMP9CTP6Cw/XSeP?POPMA5?89P6DS/XSeX7AWIWCWHX?@XE?P9P6P5GvWCW7WPWOW?WNo"). Qed.

Lemma t_writes_pick_exit_iff : forall bufs code fs tr,
  Forall (fun b => (1 <= length b)%nat) bufs ->
  (t_writes_pick bufs (t_exit code fs) tr
   <-> exists full, wpick (Z_to_bv 64 1) bufs full /\
       is_prefix tr (full ++ [ExitEv code fs])).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01bh14bufsh24codeh32fsh42trp;1p;2p;3p;6g00P3j10Tg00PXj13Tg00Q6j12Tg00B7j11Tg00h1j1:Tg00iIj29Tg00hPj28Tg019Ej35Tg00QYj16Tg00R7j27Tg01=gj64Tg00TVR0#0#0#0R1#3#2R2#1R3#1%01#0#0#3R1#2g00:Vg00Ja#1g017;#:f0R4,92'8X03f3R2553%60,71f4P2f2f1P4E4UW4W3W2W1o"). Qed.


(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs ACFG c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs ACFG c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Definition pnode_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Lemma node_ok_of_pnode : forall c I evs nx,
  cfg_transparent segs c -> pnode_ok c I evs nx -> node_ok c I evs nx.
Proof.
  intros c I evs nx Htr [Hcomp Hsound]. split.
  - intros i. apply Htr. apply Hcomp.
  - intros e st Hss. apply Hsound. exact (sstep_of_cfg segs ACFG _ _ _ Hss).
Qed.

Lemma transparent_exit_no : forall ms model x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 -> cfg_transparent segs (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc [E|E]; apply (transparent_nonalloc segs ms model x8 Hsvc); rewrite E;
    apply alloc_no_b_false; reflexivity.
Qed.

(* [comment removed for export] *)
Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok c I evs nx ->
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes c t_nil
| rz_conseq : forall c T T',
    realizes c T -> t_eq T T' -> realizes c T'.

(* [comment removed for export] *)

Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma realizes_pclosed : forall c T, realizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

(* [comment removed for export] *)

Lemma realizes_star_only : forall c T, realizes c T ->
  forall tr c', star_cfg segs ACFG c tr c' -> T tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil segs ACFG c tr c' Hh Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

Lemma realizes_admits : forall c T, realizes c T ->
  forall tr, T tr -> obs_trace_cfg segs ACFG c tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
Theorem realizes_obs_iff : forall c T, realizes c T ->
  forall tr, obs_trace_cfg segs ACFG c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
  - apply realizes_admits; exact H.
Qed.

(* [comment removed for export] *)

Lemma sstep_halted_none : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) ["WithSegs"] "p'0h02H0h11Hh22H1h32H2h42H4h52H3h62H5h71ci001ch82H6h92H7h:1li011lh;1si021sh<5modeli035modelh=2msi042msh>2sth?1eh@6model'i056model'hA2x8i062x8hB3effi073effhC3evsi083evshD4codei094codehE7model''i0:7model''hF3ms'i0;3ms'hG3sigi0<3sigp%0p;1p;4p;3p;2p;7p;6g00B7j1gTg01BTR0j41Tg00D6j30Tg00P3j1JTg00PXj1]Tg00Q6j1[Tg01GUj1XTg01WGj1WTg01aIj2fTg01aij1dTg01c1j3FTg01cmj2TTg01Khj22Tg00BWj1\Tg01H7j1RTg01A^j1QTg005Sj77j66Tg01e5j1ZTg01f=j1YTg01VPj1ITg01I=j2=Tg01gEj3;Tg01h;j1HTg01iAj2KTg01jJj2MTg01kCj1OTg002Qj6eTg01l@j1GTg01m7j19Tg00X]j2ETg01mjj2DTg01n`j1cTg01oXj3NTg00Dkj2VTg01UZj1`Tg020Sj4_Tg0213j4aTg00C7j3bTg004Fj3^Tg01E9R1f1R2f0R330p=4g01EnR4?023p=Lf2R5%`2#I;03p=3%I2=053p=<%R2=053p=8g01OKR6g01PRR7P2P3C_p=S%Q2=043p=>P1f5R8f4R9f3R:P5P2P3F7p=CP1P9P:P5P2P3E6p=@g021kR;=043p=?P4P;P9P:P5P2P3F7p=UP4P;P:P5P2P3E6p=Pg022aR<P5P2P3Ca9N9:p=:1=2390:5p=A1223#Qp=Bg00JaR=Ab=237^5p=5%g=R>p,4segsR?P5P2P3C1P0P?f7R0,4:A0>:01L:0g00TV#J#J#J#J#J#J#]#[R@#XRAf:RB%W@RC33[[[P3A<A5CA8A9C1f67RD#dREAF?891S:5,TD30f6RF/28RGfARH'4%\=R==0>HRI1>GHf9RGf8RJ'2RKfDRL'4P312BGS00fERM'4f;RN/2BROfFRP90>=RQ1>OPRRf=RS=<ACRTf?RU#RS01=0ACRVf@RW=F?URXf>RY/SS,TD50EA3A8CS02]3]2]0]6]4X71A0>=MP3PQP>P=f<RQ/2NfGRZ'>R[A<AYCR\%RWS03=0ACR]AF?HW1SUY,TD50ER^fBR_/2HR`=3ACS04]3]2]0]6X:>P3P[P412SQR[#QA<AUCA8AHCAF?_H1SWU,TD50EfCRa/2_Rb=3ACS05]3]2]0X;4P`P?P3fMRcfLRdC112LaS06=3ACS07]1X71P?P`PdfKReC1P>P=P?Q06P3PcC112MLRf=3ACS08]1X?>P?PbP=PdC1P4%Q`RgP?PfP=P3C112PM=3AC]1X>4P?Q06P=PgC1P8Q08eW1PcPFP3F7W1PcP0P3F7W1PcPJfJRgECX3^X2]X0\fHR]P3E6b0X6RPZP3E6b0W4PPP3D@b0W5P5P2P3P8P9P:O6W6W4W5W3W2W0X@7XF6X<7X=6PFP8P9P:P5P2P3O7A<A3CRRA8A5CR^AF?:5Rf%ZDRh50E129:/4SRiA0>=SRj%?SRk120F/4WRlP312J0S09/4HRmPKA0>=_Rn%?_RoA<ANCRpA8ASCRqAF?YSRr=0EhQ02]3]2]0]6]4X71P3PnP>P=%?aRsA<AQCRt%RYS0:=0ACRuAF?UYRv=0EhRw12WURx=3ACRy]3]2]0]6X:>P3PsA0EXh12HWS0;=3ACS0<]3^2V^0TX;4PxP?P3fIRhP]C1Q04]1X71P?PxP]PZC1P>P=P?P`P3PhC1Q05]1X?>P?Q0;P=P]C1P?PbP=P3C1Q07]1X>4P?P`P=P;C1P8Q05eW1PhPFP3DUW1PhP0P3F7W1PhPJPPECRzX3wX2uX0tPLP3CPb0X6oPaP3E6b0X4IP_P3D@b0W5P5P2P3P8P9P:O6W6W4W5W3W2W0X<7X=6P9P:P5P2P3O5%YDRD90EfP3PmPKA0ErDQ02]3^2q^0p^6o^4nX71P3PnP>P=A0EvDRvPy]3^2u^0t^6sX:>P3PsA0EXDQ0<]3^2V^0TX;4PzX3vX2uX0tPLP3CPb0X6oPaP3E6b0X4IP_P3D@b0X5lP5P2P3P8P9P:O6X6kX4jX5iW3X2^X0RX<7X=6P9P:P5P2P3O5%I8S0==0ACRR1=@898A0R^A;?JFS0>P0P8P9P5D:%X7Ri%H0,KFP7P8CA14OeS0?A0>Fe1MSB#O/2J/>e12YSROfNRj'4S0@P312UYS0AfORk'4S0BPxfPRl90>NRI1M_U#O/2S/>lRo%I_S0C=0ACRu1=@_S0D98ALRvA;?MaS0EPLP_PHPUD:Pi%HL,KaRzP7P_CAA3A0CS0F]4^5u]3]2]0]9]8X71A0>BkP3PIP>fQRI1MaW#O/2Y/>IRV%IaS0G=0ACRD1=@a98AMRXA;?PLREPMPaP_P:D:Pi%HM,KLS0HP7PaCARs12h]Ry=3ACRn]4^5D]3]2]0]9X:>P3PVP41MLH#O/BU%ILS0I=0ACRV1=@L98APS0JA;?ZMS0KPPPLPafVRpD:Pi%HP,KMP7PLCA12ghRq=3ACRr]4^5V]3]2]0X;4PEPMPaP_fURmD:PyP?P3fYRffXRwC112egR{=3ACR|]1X71S0LP?PyPwfWR}C1S0MP41MgZ#O/BMS0NP?P{fZP3C112deS0O=3ACR~]1X>4P?PqPfQ0NC1PFP|eW1PwP0P3F7W1PfPBPpECX4sX5DW3X2XX0DfRS0NP3E6b0X9oPQP3Eeb0W8PlP3D@b0W6P5P2P3P0PFP8P9P:O8W9W8W6W4X5RW3W2W0XC>XE7X@7XB<XA@X<7X=6PNPBPGPJP0PFP8P9P:P5P2P3O<A<A9CS0P1=@998AFA;?08PFP9P:P5D:Q0P%HF,K8%W7Ro50iQ00/4hS0QA0>=h%?h14[dS0RP314OcS0SQ0AA0>=jRO%?jS0TA<AHCR[1=@HRs98AaS0UA;?L_PaPHPWPUD:S0V%Ha,K_=0ioQ0F]4^5[]3]2]0]9]8X71A0>=cP3POP>P=%?kS0WQ0EPLP_PHPWD:ROA0izoS0E12]ZRz=3ACS0X]4^5u]3^2v^0u]9X:>Q0TP3Q0WPEPMPaP_PHD:REQ0H=0ioPn]4^5D]3^2X^0DX;4Q0EPzP?P3P}PpC1Pr]1X71P?PzPpPmC1P>P=P?PqP3P}C1P|]1X?>P?PyP=PpC1P?P{P=P3C1P~]1X>4P?PqP=P;C1P0P|eW1P}PJP3DUW1P}PGP3F7W1P}PBfTS0HECW4X5uX3OX2vX0uPlP3CPb0W9PkP3E6b0W8PjP3D@b0W6P5P2P3P0PFP8P9P:O8W9W8W6W4W5W3W2W0XC>X@7XB<XA@X<7X=6PBPGPJP0PFP8P9P:P5P2P3O;Q0>P0P8P9P:D:S0>Q0=1=@:S0P50A%GF=0ACQ0?%9J,EF=50==0>e12SG/>eQ0@P3Q0BPx%9SS0B,EN=5Q==0>lRx1B_YS0=/LlR}Q0C1=@WS0T50A%GaS0C=0ACQ0F]4]5^3O^2v^0u]9]8X71%9QRo,EB=5N==0>kP3PxP>%9Y,EQ=5S=1BaUS0F/LIS0EQ0G=0AsRx%GL=0ACRiPn]4]5^3E^2X^0D]9X:>P3Q0EP41BLWQ0JQ0KPPPLPaP_D:Q0IQ0D50A%GM=0ACPr]4]5]3]2^0VX;4PyQ0LQ0MP>%9PRV,EL=5M=S0LP?P{P3PfC1P~]1X?>P?PqQ0LPwC1P41BeZRwP?Q0O%9],EP=5Z=P3C112cd=3AC]1X>4P?P{%9Z,EM=5P=PwC1P0P~eW1PfPJP3F7W1PfPGP3F7W1PfPBPpECX4iX5xX3EX2XX0DQ0NP3E6b0X9}PIP3E6b0W8PlP3D@b0W6P5P2P3P0PFP8P9P:O8W9W8W6W4W5W3X2^X0RXD@XC>X@7XB<XA@X<7X=6PNPBPGPJP0PFP8P9P:P5P2P3O<Q0>%G8Q0P50AQ0Q%90,D8=5F==0>h12QJ/>hQ0RP3Q0SQ0A1DBo=5N==0>jRo12HS/>jRIQ0UQ0VPA%GHP@PUCAA3AFC]5]3]2^0[]8]6X71%9N,DG=5B==0>cP3PoP>Q0B,DN=5Q=Q0=/LkRN%G_Q0T50ARo12ZPRZ=3AC]5^3O^2v^0u]8X:>P3PNP4Q0FQ0C=0AsQ0X]5^3E^2X^0DX;4PZP?P3PpPmC1Pn]1X71P?PZPmQ0HC1P>%9L,D_=5a=RZP?PyP3PpC1Pr]1X?>P?PzPZPmC1P41BhMRmP?Pq1DLV=5M=P3C1P|]1X>4P?Py%9M,Da=5L=PmC1PFPreW1PpP0P3F7W1PpPJP3F7W1PpPGfSECX5oX3OX2vX0uPlP3E6b0X8IPkP3E6b0W6PjP3D@b0W4P5P2P3PFP8P9P:O7W8W6W4W5W3X2^X0RXG@XC>X@7XB<XA@X<7X=6PBPGPJP0PFP8P9P:P5P2P3O;A<A2C1=@298A:A;?95%c<R<7N:1289/4UA0>=U%?UQ09/4_P314KaQ00A0>=LRK%?LR_PAQ0:P@PQCAA;?US?NY<Q02]3]2^0t]6]4X71A0>=aP3PKP>P=%?MRKPAQ01P@PSCARSA;?WY?NU<RaQ0<]3]2^0T]6X:>P3PKPAQ03P@PYCAA;?HU?NW<Q04]3]2^0\X;4Q0;P?P3PePgC1Q05]1X71P?Q0;PgPhC1P>P=P?PbP3PeC1Q07]1X?>P?P`P=PgC1P?Q06P=P3C1Q08]1X>4P?PbP=P;C1P8Q07eW1PePFP3DUW1PeP0P3F7W1PePJP]ECX3aX2SX0TPPP3CPb0X6_PMP3E6b0W4PLP3D@b0W5P5P2P3P8P9P:O6W6W4W5W3W2W0XA@X<7X=6P8P9P:P5P2P3O6n10410010110200000087110410310;1050000000005110410300000000051104103000000000<110410310610710510:108000000000000000;1104103106107105108000000000000000<1104103106107105108109000000000000000;110410310610710510810<00000000000061104103106000000000145FA0>5F1L5FA3AGC[[[X;4X:>X71P:P5P2O3P31V191V>:1V45O3b0W1X>4W?X71o"). Qed.

Lemma realizes_step : forall c T e c',
  realizes c T -> sstep_cfg segs ACFG c e (SNext c') -> exists T', realizes c' T'.
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Lemma realizes_no_sserror : forall c T e,
  realizes c T -> ~ sstep_cfg segs ACFG c e SError.
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Definition rz_path (c : config) : Prop := exists T, realizes c T.

(* [comment removed for export] *)
Lemma rz_path_star : forall c tr c',
  star_cfg segs ACFG c tr c' -> rz_path c -> rz_path c'.
Proof.
  intros c tr c' Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros Hp; [exact Hp|].
  apply IH. destruct Hp as [T HT]. exact (realizes_step c1 T evs c2 HT Hss).
Qed.

(* [comment removed for export] *)
Theorem realizes_no_error : forall c T, realizes c T -> ~ reaches_error_cfg segs ACFG c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  destruct (rz_path_star c tr c' Hstar (ex_intro _ T H)) as [T' HT'].
  exact (realizes_no_sserror c' T' evs HT' Herr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) ["WithSegs"] "p'0h02Hfh11Hh21fh31ih42trh51xi001xi011up;1p;3p;4p;2g00B7j15Tg00MFj30j24Tg00FVj42Tg00EEj41Tg00I7j23Tg02:OR0g00Il[g00Ja#5f1R1f0R2500R3f2R4g02:oR5P1O2[P1P5P2O2R6A0041[g00F<P0f3R7P2P4O2X30R8P7P5P4O2P2P0f6R4P2f5R7O2f7P5P4O2[P2P7P5f4O2P2W0n01101000100X50P1P2O2n2001000000120100000X13P0P8P5P2C2X06C1W41402P2P5O1'3eW2o"). Qed.

(* [comment removed for export] *)
Lemma rz_silent1 : forall c c' T,
  node_ok c unit (fun _ => []) (fun _ => c') ->
  realizes c' T ->
  realizes c T.
Proof.
  intros c c' T Hnode Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
Lemma rz_emit1 : forall c c' e T,
  node_ok c unit (fun _ => e) (fun _ => c') ->
  realizes c' T ->
  realizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
Lemma rz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                       (a0 : IA) (b0 : IB),
  node_ok c (IA + IB) (fun _ => []) nx ->
  (forall i, realizes (nx (inl i)) A) ->
  (forall i, realizes (nx (inr i)) B) ->
  realizes c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply realizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply realizes_nonempty; apply (HB b0)).
  apply (rz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (rz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)

Lemma node_instr : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  node_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep.
  apply node_ok_of_pnode; [apply transparent_instr; exact Hsvc |]. split.
  - intros []. apply (sstep_instr segs ms model ms' model);
      [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros e st Hss.
    destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss) as [-> ->].
    exists tt. split; reflexivity.
Qed.

Lemma rz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

Lemma rz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                  | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)
Lemma node_write1 : forall ms model x8 buf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb.
  apply node_ok_of_pnode; [apply (transparent_nonalloc_no segs ms model x8 64 Hsvc Hno); reflexivity |]. split.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
                  [(ms_gpr ms 1, n)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model
             model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + apply write1_ok_n; assumption.
    + exact Hh.
    + apply materialize_model_accesses_no_lazy. exact Hlazy.
  - intros e st Hss.
    destruct (sstep_write_inv segs ms model x8 buf e st
                Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hss)
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

Lemma rz_write1 : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     realizes (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  realizes (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
  unfold t_write_ch.
  apply (rz_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1 ms model x8 buf); assumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - apply node_ok_of_pnode; [exact (transparent_exit_no ms model x8 Hsvc Hx8) |]. split.
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
  - apply rz_halt. cbn. discriminate.
Qed.

(* [comment removed for export] *)
Lemma rz_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  realizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                  (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  realizes (mkCfg ms model) T.
Proof.
(* [comment removed for export] *)
(* [comment removed for export] *)
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
  eapply rz_silent1; [| exact Hc].
  apply node_ok_of_pnode; [apply (transparent_nonalloc_no segs ms model x8 215 Hsvc Hno); reflexivity |]. split.
  - intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_model_accesses_no_lazy.
      exact (munmap_model_no_lazy _ _ _ Hlazy).
  - intros e st Hss.
    destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
      as [-> ->].
    exists tt. split; reflexivity.
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
Lemma cat_realizes : forall segs ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  to_wexit segs ms bufs code ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes_pick bufs (t_exit code (m_fs model))).
Proof.
  intros segs ms model bufs code Hh Hlazy Hfd Hte. revert model Hh Hlazy Hfd.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfd Hbm.
  - rewrite t_writes_pick_nil. eapply rz_exit; eassumption.
  - apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_pick_cons. eapply rz_write1; try eassumption.
    intros n Hn1 Hn2. apply IH; assumption.
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exitline_realizes_aux : forall segs ms bufs code model,
  to_wexit segs ms bufs code -> bufs = [] ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  realizes segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
  intros segs ms bufs code model Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH]; intros Hbufs Hh;
    [| discriminate Hbufs |]; intro Hlazy.
  - eapply rz_exit; eassumption.
  - eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep |].
    apply IH; [solve [assumption | reflexivity] | exact Hh | exact Hlazy].
Qed.

Lemma exitline_realizes : forall segs ms code model,
  to_wexit segs ms [] code ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  realizes segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h02Hhh15Hlazyh23Hteh34codeh45modelh52msh64segsp;1p;4p;3p;2p;9g00B7j11Tg00P3j10Tg00PXj13Tg00Q6j14Tg00BWj15Tg030Kj4<Tg01GUj1;Tg01VPj18Tg01WGj17Tg00D6j32Tg01aIj26Tg02CJj19Tg00Dkj2:Tg0391l9=Tg037U#1g01OKg00TV#0#0#0R0#0#0#0#3#4R1g01PRf3R2f2R3%30#4#1R0#5R4f1R5C<%;1%85%71321611R1#1%93%5132f6f5P4f4P2P3%10/:4P5f0M9=W1W0W2W4W3W5W6o"). Qed.

Lemma rz_wall1_mut : forall segs model,
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  (forall ms rest k, to_wall segs (Z_to_bv 64 1) ms rest k ->
     buf_modeled rest ->
     forall T : TSet, T [] ->
     (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
     realizes segs (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))
  /\ (forall ms rest k, to_wall_tail segs (Z_to_bv 64 1) ms rest k ->
     buf_modeled rest ->
     forall T : TSet, T [] ->
     (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
     realizes segs (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T)).
Proof.
  intros segs model Hh Hlazy Hfd.
  apply (to_wall_mutind segs (Z_to_bv 64 1)
    (fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
       (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))
    (fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
       (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))).
  -
    intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm T HT Hk.
    eapply rz_conseq.
    { apply (rz_node segs (mkCfg ms model) (wr_index rest)
        (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
        (fun i => mkCfg (advance_past_svc
                           (set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
                        model)
        (fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
                              (skipn (proj1_sig i) rest)) T)
        (wr_full rest Hnb)).
      - apply (node_write1 segs ms model x8 rest); assumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) T HT Hk). }
    apply t_alt_wall; [exact HT | exact Hnb].
  -
    intros ms k Hk Hbm T HT Hcont.
    eapply rz_conseq; [apply Hcont; exact Hk|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq. exact HT.
  -
    intros ms rest k Hnb Hw IH Hbm T HT Hk. exact (IH Hbm T HT Hk).
  -
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm T HT Hk.
    eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                    | exact (IH Hbm T HT Hk)].
Qed.

(* [comment removed for export] *)
Lemma wall_realizes : forall segs ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))).
Proof.
  intros segs ms model bufs code Hh Hlazy Hfd Hw Hbm. revert ms Hw Hbm.
  induction bufs as [|buf rest IH]; intros ms Hw Hbm.
  - exact (exitline_realizes segs ms code model Hw Hh Hlazy).
  - destruct Hw as [Hnb Ht]. apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_cons.
    eapply (proj2 (rz_wall1_mut segs model Hh Hlazy Hfd)).
    + exact Ht.
    + exact Hb.
    + unfold t_writes. apply t_writes_ch_exit_has_nil.
    + intros ms' Hk. apply IH; [exact Hk | exact Hbs].
Qed.

(* [comment removed for export] *)
Lemma twm_realizes_mut : forall segs,
  (forall ms model bufs code, MmapSim.twm segs ms model bufs code ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model -> bufs_modeled bufs ->
     realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
  /\ (forall ms model rest bufs code, MmapSim.twm_pend segs ms model rest bufs code ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     buf_modeled rest -> bufs_modeled bufs ->
     realizes segs (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
               (t_writes bufs (t_exit code (m_fs model)))))
  /\ (forall ms model rest bufs code, MmapSim.twm_tail segs ms model rest bufs code ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     buf_modeled rest -> bufs_modeled bufs ->
     realizes segs (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
               (t_writes bufs (t_exit code (m_fs model))))).
Proof.
  intros segs.
  apply (MmapSim.twm_mutind segs
    (fun ms model bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model -> bufs_modeled bufs ->
       realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
    (fun ms model rest bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       buf_modeled rest -> bufs_modeled bufs ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
                 (t_writes bufs (t_exit code (m_fs model)))))
    (fun ms model rest bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       buf_modeled rest -> bufs_modeled bufs ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
                 (t_writes bufs (t_exit code (m_fs model)))))).
  -
    intros ms model x8 Hsvc Hx8 Hh Hlazy Hfd Hbm. eapply rz_exit; eassumption.
  -
    intros ms model buf bufs code Hnb Hp IH Hh Hlazy Hfd Hbm.
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_cons. exact (IH Hh Hlazy Hfd Hb Hbs).
  -
    intros ms model x8 bufs code Hsvc Hno Hargs Hte IH Hh Hlazy Hfd Hbm.
    eapply rz_munmap; try eassumption.
    rewrite <- (munmap_model_fs (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model).
    apply IH; [rewrite munmap_model_halted; exact Hh
              | exact (munmap_model_no_lazy _ _ _ Hlazy)
              | apply munmap_model_fd1chan; exact Hfd | exact Hbm].
  -
    intros ms ms' model bufs code Hsvc Hstep Hte IH Hh Hlazy Hfd Hbm.
    eapply rz_step; try eassumption. apply IH; assumption.
  -
    intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb Hcont IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_conseq.
    { apply (rz_node segs (mkCfg ms model) (wr_index rest)
        (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
        (fun i => mkCfg (advance_past_svc
                           (set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
                        model)
        (fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
                              (skipn (proj1_sig i) rest))
                         (t_writes bufs (t_exit code (m_fs model))))
        (wr_full rest Hnb)).
      - apply (node_write1 segs ms model x8 rest); assumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 Hh Hlazy Hfd (buf_modeled_skipn n rest Hbr) Hbm). }
    apply t_alt_wall;
      [unfold t_writes; apply t_writes_ch_exit_has_nil | exact Hnb].
  -
    intros ms model bufs code Hte IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_conseq; [apply IH; assumption|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq.
    unfold t_writes. apply t_writes_ch_exit_has_nil.
  -
    intros ms model rest bufs code Hnb Hp IH Hh Hlazy Hfd Hbr Hbm.
    exact (IH Hh Hlazy Hfd Hbr Hbm).
  -
    intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_step; try eassumption. exact (IH Hh Hlazy Hfd Hbr Hbm).
Qed.

Lemma twm_realizes : forall segs ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  MmapSim.twm segs ms model bufs code ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))).
Proof.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  intros segs ms model bufs code Hh Hlazy Hfd Hte.
  exact (proj1 (twm_realizes_mut segs) ms model bufs code Hte Hh Hlazy Hfd).
Qed.


(* [comment removed for export] *)

Definition t_writes_ch_pick (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch ch) T bufs.

Lemma t_writes_ch_pick_1 : forall bufs T, t_writes_ch_pick (Z_to_bv 64 1) bufs T = t_writes_pick bufs T.
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Th14bufsp;1p;2g00P3j10Tg00PXj15Tg00Q6j12Tg00B7j11Tg00R]j24Tg00Dkj23Tg00TV#0#0#0#5#2#1#1g00IlR0f1f0'4,30W0W1o"). Qed.

Lemma t_writes_ch_pick_cons : forall ch buf bufs T,
  t_writes_ch_pick ch (buf :: bufs) T = t_write_ch ch buf (t_writes_ch_pick ch bufs T).
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeAlg ()) [] "h01Th13bufh24bufsh32chp;1p;3p;2g00P3j10Tg00PXj13Tg00Q6j12Tg00B7j11Tg03L3j36Tg00S[j35Tg00Dkj24Tg00TV#0#0#0R0#0#0#0#3#2%30#2#1R0%10g00IlR0f3R1f2f1f056135,40W0W2W1W3o"). Qed.

Lemma node_write_ch : forall segs ms model fd ch x8 buf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok segs (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb.
  apply node_ok_of_pnode; [apply (transparent_nonalloc_no segs ms model x8 64 Hsvc Hno); reflexivity |]. split.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
                  [(ms_gpr ms 1, n)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model
             model (map (WriteEv ch) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + eapply write_ch_ok_n; eassumption.
    + exact Hh.
    + apply materialize_model_accesses_no_lazy. exact Hlazy.
  - intros e st Hss.
    destruct (sstep_write_ch_inv segs fd ch H32 ms model x8 buf e st
                Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss)
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

Lemma rz_write_ch : forall segs ms model fd ch x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     realizes segs
       (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  realizes segs (mkCfg ms model) (t_write_ch ch buf T).
Proof.
  intros segs ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb Hc.
  unfold t_write_ch.
  apply (rz_node segs (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - eapply node_write_ch; eassumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

Lemma cat_realizes_ch : forall segs fd ch ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  to_wexit_ch segs fd ms bufs code ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes_ch_pick ch bufs (t_exit code (m_fs model))).
Proof.
  intros segs fd ch ms model bufs code Hh Hlazy Hfdc H32 Hte.
  revert model Hh Hlazy Hfdc.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfdc Hbm.
  - eapply rz_exit; eassumption.
  - apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_ch_pick_cons. eapply rz_write_ch; try eassumption.
    intros n Hn1 Hn2. apply IH; assumption.
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
