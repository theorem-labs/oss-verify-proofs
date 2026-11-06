(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Exec Cfg ITree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ITreeA () := "C46Stdlib5Lists4List2hdI46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib4LibA6ITreeA6alw_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA3alwC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init6Specif9proj1_sigC47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_appC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC59OSSVerify5KrLib4LibA5ExecF5fp_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofI47Corelib4Init5Logic2or00C59OSSVerify5KrLib4LibA8AcctCore7page_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C57Corelib7BinNums6IntDef1Z6of_natC57Corelib7BinNums6IntDef1Z3addC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib4LibA6ITreeA7acct_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib4LibA5ExecF<footprint_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4LibA8AcctCore=nonlazy_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitc59OSSVerify5KrLib4LibA6ITreeA4mrelC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4LibA8AcctCore4ainv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8AcctCore<same_but_matC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4LibA8AcctCoreBsame_but_mat_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC59OSSVerify5KrLib4LibA8AcctCoreDsame_but_mat_nonlazyC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4LibA8AcctCore4ainv01C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeI4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC59OSSVerify5KrLib4LibA8AcctCoreCsame_but_mat_haltedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State:fsst_imageC59OSSVerify5KrLib4LibA8AcctCoreBsame_but_mat_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib3Lib5ITree?is_prefix_app_lC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_monoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8evtF_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA:implF_evtFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA6tsafeAC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c59OSSVerify5KrLib4LibA6ITreeA7ptracesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree6ttraceC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA8tree_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA;tsafeA_acctC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02c59OSSVerify5KrLib4LibA6ITreeA9mrel_ainvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeIleaves_unreachable_m_stepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA9nsA_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA5mpostC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c59OSSVerify5KrLib4LibA6ITreeA7mrel_leC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib4LibA6ITreeA;node_soundA00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA=tree_atA_ainvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA=tree_atA_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeHleaves_unreachable_m_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA;mrel_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_liftC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4LibA5ExecF6csteps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA:mrel_afterC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib4LibA6ITreeA<nsA_progressC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02c59OSSVerify5KrLib4LibA6ITreeA=ttrace_existsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlgCis_prefix_app_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF5cstepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C59OSSVerify5KrLib2AS8ShapeAlg7node_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg01C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedK4ELinuxProcessSemantics?LinuxProcessSem5State5event04K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcI4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib2AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA=cstep_node_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SpinAlg;srz_silent1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF:csteps_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA4succC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS7SpinAlg9srealizes01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg5t_altC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA5s_evsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA4s_nxC1?~~~~~~~~~~~~~~~K47Corelib4Init6Specif3sig01c59OSSVerify5KrLib4LibA6ITreeA<nsA_completeC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif3sig00c59OSSVerify5KrLib4LibA6ITreeA3NSFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA3FOKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA4INV1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA3s_TC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelc59OSSVerify5KrLib4LibA6ITreeA=step_tree_atAC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC4ELinuxProcessSemantics?LinuxProcessSem3Run=obs_trace_cfgC59OSSVerify5KrLib2AS7SpinAlgAsrealizes_obs_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS7SpinAlg9srealizes03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS7SpinAlg9srealizes02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg5t_nilC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC46Stdlib5Lists4List9app_nil_rc59OSSVerify5KrLib4LibA6ITreeA8nsA_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA<succ_node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA>succ_srealizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA=node_shape_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA>node_srealizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA@csteps_srealizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA?implF_srealizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SpinAlgBsrealizes_no_errorC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA>implF_no_errorC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunEreaches_unmodeled_cfgC4ELinuxProcessSemantics?LinuxProcessSem3RunWreaches_unmodeled_cfg_reaches_error_cfgc59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA:implF_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA=implF_ret_unrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6ITreeA:implF_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import Exc.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition alw := word -> Prop.
Definition alw_le (A A' : alw) : Prop := forall p, A p -> A' p.
Lemma alw_le_refl : forall A, alw_le A A.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) [] "h01Ah11Hh21pp;1p;2p-1R0p10000p4p710p8P0p1000Gp4p710p8p1000cp4p710p1001@p4p710p8g001^j10Tg002Cj13Tg002aj12Tg003Dj21Tg004;g004o#0#0#0#0#0#0#3#2f1f0R0O1P0W1W21100eW0o"). Qed.
Lemma alw_le_trans : forall A B C, alw_le A B -> alw_le B C -> alw_le A C.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) [] "h01Ah11Bh21Ch31Hh42H1h52H2h61pp;2p;1g003Dj21Tg001^j10Tg002Cj13Tg002aj12Tg004;R0f2R1f1R2'1R3g004o#0#0#0#0#0#0#3#2f5f0R4O1P1P2f3P2P4O2O2W3W6f4/11eX53W4X20X10W0o"). Qed.

(* [comment removed for export] *)
Definition fp_le (R R' : footprint) : Prop := forall b j, R b j -> R' b j.
Lemma fp_le_refl : forall R, fp_le R R.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) [] "h01Hh11Rh21bh31jp;2p1005Tp4p70R0p1006Dp4p710R1p8P0p1006^p4p710R2p8P0p1007:p4p710R3p8P0p1007Xp4p7210R4p8P0p10085p4p710R5p8P0p1001@p4p710R6p8P0p1008UR0p4p710R7p8p10092p4p70R8P1p8P8P2p8P8p1009`p4p710p8P8p1000cp4p710p8P8P3p8P8p100:Vp4p710p8P8P4p8P8p100;Qp4p710p8P8p100<Kp4p710p8P8p100=Gp4p710p8P8P5p8P8P6p8P8P7p8P8P0p4p7210p8P8p100>Ap4p710p8p100>^p4p7210R8P1p8P8P2p8P8P3p8P8P4p8P8P5p8P8P6p8P8P7p8p100?Jp4p70R8P1p8P8P2p8P8P3p8P8P4p8P8P5p8P8P6p8P8P7p8g00@@j20Tg00A6g00Aog00BMf2f1f0R7O2P7W0W3W21077eW1o"). Qed.
Lemma fp_le_trans : forall A B C, fp_le A B -> fp_le B C -> fp_le A C.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) [] "h01Ah11Bh21Ch31Hh42H1h52H2h61bh71jp;2g00@@j20Tg00A6R0f2R1f1R2'0R3g00Aog00BMf6P2f0R4O2f3P1P2f4R5P1P2P4O3O3W3W7W61051eX53W4X20X10W0o"). Qed.
Lemma rng_fp_le : forall R R' lo len, fp_le R R' -> rng R lo len -> rng R' lo len.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) [] "h01bh11jh22H0h31Ah41Bh51Hh62HLh72Hbh82Hjh91Rh:2R'h;3lenh<2lop;2p;3p;1p;4g00@@j29Tg00Blj34Tg00C_j20Tg00D;j21Tg001^j12Tg00DXj16Tg00E6j28Tg00ESj17Tg00F3R0j23Tg00FNj45Tg00A6R1g00AoR2f3R3f2R4'9f4R5f1R6744P0g00FiR7/031134g004o#2R8#6%28#2#2#2#2#6'8R8'0g00BMR9f5R:/06%76,14R;f6R</1:R='0f9R>P3P4O2[[]1^02'3A4:53f0R?107:10=8f8R=/0611>=R@,0;f<RAP3P4O2[[^19^02'3P0f7R0/1</0810>6f:R</1>,0;f=RBP3P4O2[[^19^02A4>=0P?10@810A611BA,0;f@P3P4O2RA[[^19^02f;R@,0711@</08R810B6R@f>/1B,0;R;PA[[^19^02RA'3P:P8PAP6PBP3P4P5P3P4P6P?O4O3X8;X7@X19X02C5C5W5W4P6P?O2n2001000000120000000W2W3P6P?O2n2001000000121000000W2W6X;2W<X:1W9o"). Qed.

(* [comment removed for export] *)
Lemma fp_ok_mono : forall lz lz' (A A' : alw),
  (forall p, page_in_ranges p lz' = true -> page_in_ranges p lz = true) ->
  alw_le A A' ->
  fp_le (fp_ok lz A) (fp_ok lz' A').
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) [] "p'0h01Eh11ph21Ah32A'h42ALh51Hh62H0h72Hbh83Heqh92Hkh:2LEh;2NLh<3SUBh=1bi001bh>2b0h?1eh@1jhA1khB2lzhC3lz'p;1p;2p;4p;3p;6g001^j14Tg002Cj1PTg002aj1BTg00GGj2>Tg00Ggj1OTg00HGj20Tg003Dj2ATg00IDj4:j2;Tg00J9j2?Tg00C_j2=Tg00DXj18Tg00E6j2<Tg00JQj2NTg00F3j2MTg00ESj13Tg00D;j22Tg00Jmj11Tg00KhR0j2FTg00LBj3ETg00M<j29Tg006Dj36Tg00MVj1CTg00N8j2DTg00NWj4@Tg007:j6GTg006^j6HTg00O3j2ITg00ORj3JTg00Olj3KTg00@@j2LTg00PFR1f0R2g00PfR336p=7g00QFR49612p=5g004o#4R5#4#4#4#4#4R6#P#BR7/>7#OR8g004;R9f3R:,02#7f1R;f5R<'0#7[^17f2R7/A;g00Aog00BMR=f7R>P<P;P2C:1?27g00Fif4R?'=%85%86'<,N?'MP:P7P;P2O3%37,2<#1R6f;R5'0#5f9R@P6O1'FP0f6R0%3:'2#1R6f<RA'0#5f:RBP6O1%3?,2>#1R69EABP2f=RC,06#5f8RD%3<'2#1RE/0CRF#5RGP5PEO1RHPFP11912%30,2@#1f>'0=612P1%3D,25#1RDf@'0=612%5;]0P;%3>,2B#1f?'0RB#7PCPDP2O2fA,0D#7P1P3%C@,DA#1fB'0RAP4P1PAP3P2C@P?EGA6134RAP1P3P1p-0P2g00Qfg00RBR3n0110000020000X?1g00R_P4P2EHP31IA2b6b8b0W0%5B1914W0n0110000020000P2O1b0b>3JW;P2O1P5P6O1P@PEP2O29KGHW4P2O1n200100000021000010000b1W7W9XA=P>P<P7P;C:eW5W@W=1;<:1;?7'LeW:W<X39W2XC8WBo"). Qed.

Section ITreeA.

Variable node : Type.
Variable segs : list Segment.

(* [comment removed for export] *)
Variable at_node : node -> footprint -> machine_state -> Prop.
(* [comment removed for export] *)
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
(* [comment removed for export] *)
Variable fstep : node -> resp -> footprint -> footprint -> Prop.
(* [comment removed for export] *)
Variable NMAX : nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrel (A : alw) (mo mo_ : Model) : Prop :=
  same_but_mat mo mo_ /\ m_vm_materialized mo = [] /\
  List.NoDup (m_vm_materialized mo_) /\ (forall p, List.In p (m_vm_materialized mo_) -> A p).

(* [comment removed for export] *)
Definition acct_ok (RNG : footprint) (A : alw) (mo : Model) : Prop :=
  footprint_ok (m_vm_lazy mo) A RNG /\
  (exists L, List.NoDup L /\ (List.length L <= NMAX)%nat /\ forall p, A p -> List.In p L) /\
  (nonlazy_bytes mo + Z.of_nat NMAX * page_size <= vm_limit (m_vmmaps mo))%Z.

Lemma mrel_ainv : forall RNG A mo mo_,
  acct_ok RNG A mo -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "h01ph11Hh21Lh31Ah42ALh53CANh63FINh73FOKh82LZh92NDh:3RNGh;4ROOMh<2SBh=2VMh>2_Hh?3_H0h@2mohA3mo_hB1vhC1zp;3p;1p;2p;4p;6p;9g00S;j3[Tg00T3j10Tg00Tkj3LTg001^j1ETg002Cj1ZTg002aj1UTg00Ggj1NTg000Gj2@Tg00Ugj2TTg00VGj2RTg00Vaj3>Tg00W8j2JTg00WRj1BTg00ESj1XTg00XRj2VTg00D;j2HTg00Xoj12Tg00Yfj1GTg00C_j2FTg00F3R0j2;Tg00Z]j3KTg00[Rj4<Tg00\Kj2MTg00]Jj1:Tg00^Jj1STg006Dj33Tg00^jj3QTg00_oj1ITg00GGj2PTg00`bj18Tg00aUj16Tg00bJj17Tg00c?j15Tg00d3j19Tg001@j6OTg00dhj3YTg00eol9WTf2R1f1R2f0R3';';p=1f3R4?312/;3p=4g00fh?323p=Ag00g`?323p==g00hX?323p=?g00iR?323p=Cg00jK?323p=Dg00A6g004;g00kER5A[412P0%01f4R67L4g004o#E#E#E#E#E#E#Z#UR7#NR81@73R91T73p,4NMAXR:'RR;f5R<P3O1A>721R=[^0731X28'J%B1%X:g00l;'VR>'H%21#G'F';AK641%06R6P<P:P4C<[P3f6R49L6<f8R6P3O1P=[^07919;X28,J8%B</H>%2<#G'F';P0f9R1P3O1P=[^07919;X28,J8%B4/H>%24#G'Ff7R?=K64%06P1P:P?C<[P3f;R?P3O1P=[^07919;X28,J8%B1/H>%21#G'Ff:R;=K?1P01M?;P8%:?R9%S7R=%:;,@7A>739f>R9P2O1[^07';C4f<R;#0f=R6P:P?C<P31M6;P8%:9R;P=%:6,@7A>73;fAR?P2O1[^07';C4P0f?R4#:R@=38=1@7;A>73@fBR@P2O1[^07';f@#0P?P:P4C<P3%:?R?=38=1@7?%:@R@9>73fER?P2O1[^07';P01@7@fCR@#:9>73fFR=P2O1[^07fDR8#0P?P:P@C<P3%:8,@7%:=9>73fIR8P2O1[^07fGR@?Q=1g00m3R1%I=%I@R?g00mkR4%2=%2@R;1P77#NR7%0=%0@RA%8=%8@RB'A%6=%6@RC'=%7=%7@RD'?%5=%5@RE'C%9=%9@R@'D3131C4C4C4P0fHRF#I931?P4P;%2FP7PA%0F%8F,AB%6F,=C%7F,?D%5F,CE%9F,D@3131C4C4%08fJR@P:PFC<P3%I8%I@531P4%2@fKR1#2R8P7%0@%01RF%8@%81RE'A%6@%61RD'=%7@%71RC'?%5@%51RB'C%9@%91RA'D3131C4C4P0fLR;#29348P7PF%0;%8;,AE%6;,=D%7;,?C%5;,CB%9;,DA3131C4fMRA#0fNRBP:P;C<P3%2A%2B534P7%0BfORA#0R;%8B%8ARC'A%6B%6ARD'=%7B%7ARE'?%5B%5ARF'C%9B%9ARA'D3131C4P0fPR0#0937;%80,AC%60,=D%70,?E%50,CF%90,DA3131fQ#0RAfRRFP:P0C<P3%0F937A%8FfSRA#8'A%6F%6A'=%7F%7A'?%5F%5A'C%9F%9A'D3131fTRF#0fUR7P:PAP2P9P6P1g00AoR1%BF1H3>%2FR6#G'FXC1P4P6%B7/H>%G3'FXB4P@%2AP<EO%BAAYFA=EOM9WW?W8P2P3O2n2001000000120000000W1W=P2P3O2n2001000000121000000W1W>P2P3O2n2001000000121000000b1W4W9P2P3O2n2001000000121000000W1W5P2P3O2n2001000000121000000W1W<P2P3O2n2001000000121000000W1W;W6P2P3O2n2001000000121000000W1W7P2P3O2n2001000000121000000W1XA5W@W3W:o"). Qed.

Lemma mrel_halted : forall A mo mo_, mrel A mo mo_ -> m_halted mo_ = m_halted mo.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "h01ph11Ah21Hh32SBh42_Hh52moh63mo_p;3p;2p;1g00Z]j3>Tg00\Kj26Tg001^j10Tg002Cj18Tg002aj1=Tg00Ggj1;Tg00]Jj11Tg00^Jj19Tg006Dj33Tg000Gj25Tg00Vaj34Tg00F3R0j22Tg00nbj1:Tg00oDj17Tg010;j3<Tg004;g00kER1f2R2f1R3f0R43>P01623g004o#0#0#0#0#0#0#8#=R0#;R5%12R6%90R733%13,50A4046f5R6P3O1[^00'2'2%:0%72f3R2#733P4f4R8/62%16R2=357%18,50A4042f8P3O1[^00'2'2f6?<63W4W3P3P4O2n2001000000120000000W2X61W5W1o"). Qed.

Lemma mrel_fs : forall A mo mo_, mrel A mo mo_ -> m_fs mo_ = m_fs mo.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "h01Hh12_Hh21ph31Ah42FSh52SBh63_H0h73_H1h83_H2h93_H3h:1fh;2moh<3mo_p;3p;2p;1p;6g00Z]j3PTg00\Kj2HTg001^j1@Tg002Cj1JTg002aj1OTg00Ggj1FTg00]Jj1BTg00^Jj1KTg000Gj2ETg00Vaj3DTg00F3R0j2=Tg011Aj16Tg00^jj3NTg00_oj1ATg00Xoj1<Tg00GGj2LTg00T3j19Tg00`bj14Tg00aUj10Tg00bJj11Tg00c?j12Tg00d3j13Tg006Dj35Tg0124j1CTg00M<j2ITg001@j6MTf3R1f2R2f1R335f0R4'=p=7g0092R5?534p=>g00fh?534p=;g00g`R6?534p=:g00hXf5R7f4R835g00iR?512g00jK?534'='=p=81=34,=2p=?A5623/=4p=Gg004;g00kER9AP234P01H23g004o#@#@#@#@#@#@#J#OR:#FR;%B2R<%K:R=%B3,E:AD:4<P7P3O1[^2:'=C7%62%61'>P41H81P;%B7R;P=%B8,E:AD:4;f8R;P3O1[^2:'=C7f6R8?N73g00m3R=%A7%A8R1g00mkR2%<7%<8R<1L::#FR:%97%98R>%47%48R?';%07%08R@':%17%18RA%27%28RB%37%38R8E83?C7C7C7P0f7R7#A95=1P2P<%<7P:P>%97%47,;?%07,:@PA%17PB%27P8%37E83?C7C7%67%6;'>P4%A;f9R;#A55=P2%<;f:R=#<R7P:%9;%9=R8%4;%4=RB';%0;%0=RA':%1;%1=R@%2;%2=R?%3;%3=R=E83?C7C7P0f;R;#<9527P:P8%9;%4;,;B%0;,:AP@%1;P?%2;P=%3;E83?C7%6;f<R;#6'>P4%<;f=R;#<552P:%9;f>R2#9R=%4;%42R?';%0;%02R@':%1;%12RA%2;%22RB%3;%32R2E83?C7P0f?R;#995:=%4;,;?%0;,:@PA%1;PB%2;P2%3;E83?%6;f@R;#6'>P4%9;fAR;#955:%4;fBR:#4R2';%0;%0:RB':%1;%1:RA%2;%2:R@%3;%3:R:E83?P0fCR;#4,;2%0;PA%1;P@%2;P:%3;E85GB%6;fDR;#6'>P4%4;fER;#4';%0;fFRB#0R:%1;%1BR@%2;%2BRA%3;%3BRBE83GP0fGR0#0,::P@%10PA%20PB%30E8%60fHR0#6'>P4%00fIR0#0':%10fJRB#1%20%2B%30%3BE8P6fKR0#0RA%C4fL#0#C'>X:6%CA,I5%0BP3EM%6B%60'>eW9W4P3P4O2n2001000000120000000W0W8P3P4O2n2001000000120000000W0W7P3P4O2n2001000000121000000W0W6P3P4O2n2001000000121000000W0W1P3P4O2n2001000000121000000b0W1W5P3P4O2n2001000000121000000W0X<9W;W3o"). Qed.

Lemma mrel_le : forall A A' mo mo_, mrel A mo mo_ -> alw_le A A' -> mrel A' mo mo_.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "h01ph11Hh21Ah32A'h42ALh53CANh62Hph72LEh82NDh92SBh:2moh;3mo_p;3p;2p;1p;4g00Z]j37Tg00\Kj29Tg001^j14Tg002Cj1:Tg002aj1=Tg00Ggj1<Tg00]Jj10Tg00^Jj1;Tg006Dj35Tg000Gj23Tg00Vaj32Tg00F3R0j21Tg003Dj26Tg00FNj48Tg004;R1g00kER2f3R3f1R4f0R537P0f2R6/94g004o#4#4#4#4#4#4#:#=R7#<R8%06R9%;7R:35%04,37A2759f6R9P4O1[^07'1'1f5R;f4R<'6A7;<3[P519<3%0;R;=58:%0<,37A275;f9R<P4O1[^07'1'1P0%09R==58:137;A275=f:R=P4O1[^07'1f8R;,6<f797<;[P5%0;R;=58:137;%0<R<9275f=R;P4O1[^07'1P0137<%0=9275f>R<P4O1[^07f<R0,6;f;R>97;0[P5%0>,37%0;9275fAP4O1[^07f@f?R;'619;<%0;R;=58:R:%0<,37R<A275;R;fBP4O1[^07R8'1R>'1P=P:P>P9P<P8P6P6P4P3P4P5O2O2X6;X07C8C8C8W7W4W8P4P5O2n2001000000121000000W1W5P4P5O2n2001000000121000000W1W9P4P5O2n2001000000121000000W1X;2W:X31W2o"). Qed.

(* [comment removed for export] *)
Lemma mrel_after : forall A mo mo_ mo_',
  mrel A mo mo_ -> same_but_mat mo_ mo_' -> ainv (m_vm_lazy mo) A NMAX mo_' -> mrel A mo mo_'.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "p'0h01ph11Hh22_Hh33_H0h41Ah52ALh63CANh73INVh81Lh92NDh:2SBh;3SB'h<3_H1h=2moh>3mo_h?4mo_'i008ai_allowi016ai_fini027ai_lazyi038ai_nodupi047ai_roomp;3p;2p;1p;4p;5g00Z]j39Tg00\Kj25Tg001^j16Tg002Cj1<Tg002aj1JTg00Ggj1;Tg00]Jj10Tg00^Jj1?Tg006Dj37Tg000Gj21Tg00Vaj32Tg00F3R0j23Tg00T3j14Tg00[RR1j48Tg012mj5ITg00GGj2HTg00Ugj2GTg00VGj2FTg00W8j2ETg00WRj1@Tg00ESj1ATg00XRj2BTg00D;j2>Tg00Xoj1CTg00Yfj1DTg00C_j2=Tg00FNj4:Tg004;g00kER2f3R3f2R4f1R539P01534R6g004o#6#6#6#6#6#6#<#JR7#;R8%03R9%?7R:37%04,17f0R;=279f6R9P5O1[^07'3'3f5R<#4P9p,4NMAXR=P3C8f7R>f4R?799[\6P;15<?%09R6=78:%0<,17A27;6f9R<P5O1[^07'3'3P0%0>R@=78:1176A27;@f:R@P5O1[^07'315>9%4<P@P=P>C8f;R9f879@[[P;%0<R<=78:117<%0@R<927;f=R6P5O1[^07'3P0117<%09927;f>R<P5O1[^07159@%46P<P=P9C8f?R@f<R079<[[P;%00,17%0<927;fAR0P5O1[^0715<6f@R6#4P0P=P<C8150@%00R<=78:R:%0@,17%06RA927;fDRBP5O1[^07'3RC'3P0P6P@P9P5DIP:PCP>P1%40fBP=P@117AA27;<fER<P5O1[^07'3P;1H77#;%4BfF#437%0<,17fG#0927;fKP5O1[^07117;1G7;/F=fLP;O1A2754[^07'3'3X88,E8fHR8#@%A=g00l;'B'>%C8#D'=fI#0,17fJ#0927;fNP5O1[^07P3P4C:W<W3W5W9W2P?P3P4P5P;O5n400001000000151102103100101104C:C:W7W;W3W2P5P;O2n2001000000121000000W1W6P5P;O2n2001000000121000000W1W:P5P;O2n2001000000121000000W1X?2X>2W=W4o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mpost (A : alw) (mo' mo_' : Model) : Prop := mrel A mo' mo_'.

Record node_soundA : Prop := {
  (* [comment removed for export] *)
  nsA_pending : forall n RNG ms, at_node n RNG ms -> ms_svc_pending ms <> None;
  (* [comment removed for export] *)
  nsA_complete : forall n RNG A ms mo mo_ evs X,
      at_node n RNG ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      footprint_ok (m_vm_lazy mo) A RNG -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_ ->
      sstep_cfg segs ACFG (mkCfg ms mo_) evs X ->
        (exists rsp mo' mo_', X = SNext (mkCfg (nret ms rsp) mo_') /\ nstep n mo rsp mo' evs /\ mpost A mo' mo_')
     \/ (exists code mo' mo_', X = SNext (mkCfg ms mo_') /\ nexit n mo code mo' /\
                              evs = [ExitEv code (m_fs mo')] /\ m_halted mo_' = Some code);
  (* [comment removed for export] *)
  nsA_sound : forall n RNG A ms mo mo_ rsp mo' evs,
      at_node n RNG ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      footprint_ok (m_vm_lazy mo) A RNG -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_ ->
      nstep n mo rsp mo' evs ->
      m_halted mo' = None /\ minv mo' /\
      exists mo_', sstep_cfg segs ACFG (mkCfg ms mo_) evs (SNext (mkCfg (nret ms rsp) mo_')) /\ mpost A mo' mo_';
  nsA_exit : forall n RNG A ms mo mo_ code mo',
      at_node n RNG ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      mrel A mo mo_ ->
      nexit n mo code mo' ->
      m_halted mo' = Some code /\
      exists mo_', sstep_cfg segs ACFG (mkCfg ms mo_) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo_')) /\ m_halted mo_' = Some code;
  (* [comment removed for export] *)
  nsA_progress : forall n RNG A ms mo mo_, at_node n RNG ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      footprint_ok (m_vm_lazy mo) A RNG -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_ ->
      (exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo')
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint implF {R} (RNG : footprint) (t : itree node R)
    (Q : R -> footprint -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match t with
  | Ret r => evtF segs RNG (Q r RNG) ms
  | Vis n k => evtF segs RNG (fun ms1 => at_node n RNG ms1 /\
                 forall rsp RNG', fstep n rsp RNG RNG' -> implF RNG' (k rsp) Q (nret ms1 rsp)) ms
  end.

Lemma implF_ret_intro : forall {R} RNG (r : R) Q ms, evtF segs RNG (Q r RNG) ms -> implF RNG (Ret r) Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "h01Qh11Rh23RNGh32msh41rh51xh62x0p;4p200R0p10142p60551111002p8g014hj40Tg00A6R1f1R2f2R3g015\R4p-0[^61]5p,4segsf3R1P2P3P1O2f0R1C0P1UX34W0W4W2X10o"). Qed.

Lemma implF_mono : forall {R} RNG (t : itree node R) (Q Q' : R -> footprint -> machine_state -> Prop) ms,
  implF RNG t Q ms -> (forall r RNG' ms', Q r RNG' ms' -> Q' r RNG' ms') -> implF RNG t Q' ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "h04RNG'h13rsph23RNGh31Qh42Q'h52msh63ms1h73ms'h81rh91Hh:2HQh;1th<2H'h=2H0h>2HFh?3Hath@2HkhA2IHhB1RhC1khD1np;2p;5p;3p;7p;4p10092p4p70p1016cp4p710p8p,4nodeR0p4p300g017aR1p4p710p8p200R2g018WR3p4p7210p8P2g0142R4p60551111002p8P1j23TP4j50Tg019Oj35Tg01:Ej74Tg01;>j46Tg01<4j21Tg00F3R4j22Tg00FNj48TP3j77Tg00A6R3f1R1,30P0f2R51305f4R6g015\R7p-0[\3R8[R9f5R:P8[R;f7R<f3R=P6P5f0R>D0f8R?f6R@P5P1P>O3P@P=P5P1O3[^77^03RA]8RBf9RCP:P@P=P5D0[[^57]4]3^23W;P<P=A50<6P5P>D0p,4segsRDP:P6P@P:O2P=P@P:O2P5P1P:P<P@P>O3REP5P?P<P1P>O4W<X77P:P?P<P1O3\E^77eF4PCP:A50C@P=P5D0eX:BW9X57X4;X39X23X85g01<gR91306[P8\@R;P8\<R8PCP=P:P6O1P5P>D0f:RBPA]8RAf;REP:P<P@O1P=P5D0[[^57]4]3^23\9PCP=P0PCP@P:C6P5P>D0PDP:p,7at_nodeRDPCP@P>O3R@p,5fstepRFPEP1P?P>O4RGf?RHP1PEP5O1RIP?11=5RJD0[^03^19'2X67PHP1PIP<PJD0\G^03^19,2@X67P5P1PDPBP<P>O3PFf<R@P1PCP>O4RGf@RIP1P@P5O1RKPCPJD0[^03^19'2X67P>O1P4PDPBP<P1O3PIP1PKPC1165D0\G^03^19PDPEP?P5O3PFf=RGP1PBP>O4fAP1PGP5O1PC11:5D0[^03^19'2P>PDP@PCP=O3PFPHP1P@P>O4fCP1PHP5O1P@11<5D0[^03^19PDf>PEP:O3PFPIP1PGP>O4RFfDP1PIP5O1P@11?5RID0[^03^19P1PHP5P1PGP@PIP=P5P1P>O3PCO7X>FX03X19C8W@W?P1P>O2n2001000000120000000W=X67F4PEP:P0PEP?P<C6P=P5D0eX:AW9X57X48X3;X23WAWCXD0P>P1F7W;W2XB2o"). Qed.

(* [comment removed for export] *)
Lemma implF_evtF : forall {R} RNG (t : itree node R) Q P ms,
  evtF segs RNG P ms -> (forall ms', P ms' -> implF RNG t Q ms') -> implF RNG t Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "p'0h01Kh13ms'h21Hh31Ph41Qh51Rh63RNGh74RNG'h81ki001kh92msh:3ms1h;1ni011nh<1ri021rh=3rsph>1ti031ip;2p;4p;5p;3p;7p200R0g0142R1p60551111002p8g017aR2j22Tg014hj47TP1j50Tg019Oj31Tg01=Zj74Tg01;>j43Tg01<4j26Tg00F3j25Tg00A6R1p,4nodeR3f1R4'2f2R5g015\R6p-0[R7\1[p,4segsR8f4R9P4f0R:C7f3R;P:O1f8R<f7R=f6R>f5R?P4D0[^16P2P3P=P?P:O1f:R2f9R@P5P=P4D0[^16P@P<P4P>P9D0]0P?P>P:O1f;RAP2A13A5P<P4D0[^16P8P@P>P=P4P@O2P?P9P:F4P2P@A1324P=P?D0eW0X<<P:O1g01<gR9123A[P<P:O1f=RBf<RCP3PBP;P5C3P2P4D0[^16P8PAP<p,7at_nodeP;PCP:O3p,5fstepP?P4f>P:O4f@P4P?P5O1PB16;5D0[^71^=9'5X:6P=P>P:F4PCPAP3PCP5P4C3P@P=D0eW0W8X;3P4P:O2n200110300021010220101100P:O1W0W2X96X37W4W>W6X50o"). Qed.

(* [comment removed for export] *)
Lemma implF_bind : forall {A B} RNG (t : itree node A) (f : A -> itree node B) Q1 Q ms,
  implF RNG t Q1 ms -> (forall r RNG' ms', Q1 r RNG' ms' -> implF RNG' (f r) Q ms') -> implF RNG (bind node t f) Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "h04RNG'h13rsph23RNGh31Qh42Q1h51fh62msh73ms1h83ms'h91rh:1Hh;2Hfh<1th=1Ah>1Bh?2H0h@2HFhA2HQhB3HathC2HkhD2IHhE1khF1nhG1xp;2p;5p;3p;8p;4p;7p200R0g018WR1p4p7210p8P0g01>RR2p4p7210p8P0g0142R3p60551111002R4p8p201R5P2p4p73110p8P5P4p8P5g01?ER4p60551111002p8g017aj24TP3j50TP2j51Tg019Oj36TP4j8:Tg01;>j45Tg01<4j22Tg00F3R4j23Tg00FNj49Tg01:Ej78TP1j77Tg00A6R1p,4nodeR2f2R3'4P2f3R61426f5R71427R8[R9f6R:g015\R;p-0[\1R<[R=f9R>f4R?P7P3f0R@D0f:RAP:P3f1RBP@O3RCf=RDP3f8REP6O1RFP:PBD0[^8;^01]9RGPAP:P2f;RHPAf7RIP7D1P6P3D0[[^6;^3=]4]5^21W<P>P?A62>7P3P@D0PAP:P7PIO1P6P?PIP:O2P3PBP7PEPIP@O3P3P>PEPBP@O4WAX8;G:PAP:P2PHPAA62HIP7D1P6P3D0eX;GW:X6;X3=X4=X59X21X96g01<gR9P8[142I\IR8P<\ER<PHP?P:P7O1P3P@D0f<R=f?RGP3PFP:PBD0\C^8;^01]9RCP=P:P2PDP=PEPIO1P7D1P6P3D0[[^6;^3<]4]5^21\9PHP?P2PHPIP:C5P3P@D0p,4segsP:p,7at_nodeRFPAPIP@O3RJp,5fstepRKP=PBP>P@O4RLfARMPBP=P3O1RNPE1263ROD0[^01^19'3X7;f@RPPBP2PMPPPNP>D1PIPOD0\L^01^19,3JX7;P3PBPFPHPEP@O3PKPDPBPAP@O4RJfBRLPBPDP3O1RNP>POD0[^01^19'3X7;P@O1P4PFPHPEPBO3PLPBPNP>12?3D0\J^01^19PFP=P>P3O3PKf>RJPBPHP@O4PLPBP2fCPLPJP3O1PHD1P>1273D0[^01^19'3P@PFPDPAP6O3PKPPPBPDP@O4fERAPBPPP3O1P=12I3D0[^01^19PFPGP=P7O3PKPMPBPJP@O4RKPAPBP2fFPAPMP3O1PJD1P=12E3RMD0[^01^19PBPPP3PBPJPDP=PMP6P3PBP@O3P>O8X@KX01X19C9WCWBPBP@O2n2001000000120000000W?X7;F8P=P:P2P=P>P2PJPDP>P@O1P:D1XG9C5P6P3D0eP=P:P2PDP=P2PDP>PEC5P7D1P6P3D0eX;CW:X6;X3<X4<X58X21WDWEXF2P@PBF7W<W2X>5X=0o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint tsafeA {R} (RNG : footprint) (A : alw) (t : itree node R) (mo : Model) : Prop :=
  acct_ok RNG A mo /\
  match t with
  | Ret _ => True
  | Vis n k => nsafe n mo /\
      forall rsp mo' evs, nstep n mo rsp mo' evs ->
        exists RNG' A', fstep n rsp RNG RNG' /\ alw_le A A' /\ tsafeA RNG' A' (k rsp) mo'
  end.

Lemma tsafeA_acct : forall {R} RNG A (t : itree node R) mo, tsafeA RNG A t mo -> acct_ok RNG A mo.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "p'0h02moh11Ah21Rh33RNGh41ti001th52A'h61Hh74RNG'h83evsh93mo'h:3rsph;1ki011kh<1ni021nh=1ri031ri041ii056tsafeAp;2p;5p;3p;4p;1p200R0g01@@R1p605611111001R2p8g017aR3j25TP1j53Tg00S;j31Tg019Oj37Tg01A7j36Tg01;>j49Tg00Ggj18Tg003Dj24Tg00F3j20Tg00W8j22Tg00A6R1g004;R4p,4nodeR5f2R6'5R7P3P5f3R8g00kER9f5R:f4R;P8f1R<f0R=D3A1:;<[]0P=f6R>P:P;A75><P=D3A1>:<g00QfR?;6=W6X09X=;P=O1g01<gR@f7RA,55[f8RBPAP>P5PBP6P<C9P=D3A1BA<p,5nsafeRCP8P<O2g01AR#8RDp,5nstepREP>P;P6P<P=O5p,5fstepRFf9P:f>P<O4f=RG/4=p-0RH^09^47^14^31^22A186=P3P5P;PHP<P?PCP<P6O2PEP;P:P6P<P=O5PFPAP:f;P<O4f:/4=PGf<P<P=P>P:O1P;O5'0'0X54,24X71,21[^8D^99^:@'0n200110000021010320102101'0X09X47X14X31X22p?1003105f?P<P=PBP:O1P;O5'0'0X54,24X71,21[]8^99^:@'0;6=W6X09W;X<5P<P=O2n200110400021010320102101W4W1W3X20o"). Qed.

(* [comment removed for export] *)
Definition ptraces {R} (t : itree node R) (mo : Model) : ShapeAlg.TSet :=
  fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tree_atA {R} (RNG : footprint) (A : alw) (t : itree node R) Q
    (ms : machine_state) (mo mo_ : Model) : Prop :=
  implF RNG t Q ms /\ leaves_unreachable_m nstep t mo /\ m_halted mo = None /\ minv mo /\
  tsafeA RNG A t mo /\ mrel A mo mo_.

Lemma tree_atA_ainv : forall {R} RNG A (t : itree node R) Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "h01Hh11Ah22MRh31Qh41Rh53RNGh62TSh72_Hh83_H0h93_H1h:3_H2h;2moh<3mo_h=2msh>1tp;2p;8p;5p;1p;3p;4p;6p101BHp6054111000p101C@p4p741110p8g01D5R0p605911111111002R1g0142R2p60551111002p8P1g01@@R3p605611111001p8P1g01DnR4p4p73110p8p200R5g01F1R6p605611111000p8P5P1p8g017aj2CTP0j8BTP2j5;TP4j58Tg001^j13Tg002Cj1ATg002aj1>Tg00nbj1=Tg00oDj14Tg01Fmj1<Tg006Dj35TP3j52Tg00Z]j30Tg00T3j17Tg00[Rj46TP6j6@Tg01GOj6?Tg00F3R6j2:Tf2R3f1R4f0R2':':p=1f5R0f4R1f3R7P3P4D2/:2p=9g00A6R8g004;p,4nodeR9/C3g015\R:p-0[\8\7g00kER8f7R;f6R<P0P1P7P3P4P2GBP6f8R=P;P0P1P7D;P9p,5nstepR>P=P0P3D8g004o#3#3#3#3#3#3#A#>R?#=R@%43%<?R?35p,4minvRAP3O1P=P;P<P0P3D2A0<343131%77P;p,4NMAXR7P3C6P2f:R3f9RBP;P<P0D;P9P>f;RCP=P0D8%40=5@?PAP0O1PCP3PBP=P0D2A0B013131P6P9P>f<R1PBP<D8%4<=5@?PAP<O1P1PCP3PBP<A03<0E931%7;PCP7P<C6P2P9P>f>R>PCP=D8%4B=5@?PAPBO1f?R9P>f=R<P1PBA0<B=E931P6%43=5@?PAP3O1f@R=P9P>P<P3D2A0>3B31%7CP9P7P3C6P2%41=5@?PAP<O1fCR?fBR@fAR3P=P<D2A03<131P6PAP>O1fDR1P?P@P3P>A0@><E9%79P?P7P>C6P2PAP=O1fGRAfFR>fER9P1P3A093=E9P6fHR6PAP>P9P@D2A0>@3%7?PAP7P@C6P2fJR@fIR7P6PAP1D2A0791fKR1P@P>P9fLP1P@P7P>P4E@P2E?W2W6P4P2O2n2001000000120000000W0W:P4P2O2n2001000000120000000W0W9P4P2O2n2001000000120000000W0W8P4P2O2n2001000000121000000W0W7P4P2O2n2001000000121000000W0X<8W;X=:W3W>W1W5X45o"). Qed.

(* [comment removed for export] *)
Lemma tree_atA_step : node_soundA -> forall {R} RNG A n (k : resp -> itree node R) Q ms1 mo mo_ rsp mo' evs,
  at_node n RNG ms1 -> (forall rsp RNG', fstep n rsp RNG RNG' -> implF RNG' (k rsp) Q (nret ms1 rsp)) ->
  leaves_unreachable_m nstep (Vis n k) mo -> m_halted mo = None -> minv mo -> tsafeA RNG A (Vis n k) mo ->
  mrel A mo mo_ ->
  nstep n mo rsp mo' evs ->
  exists RNG' A' mo_',
    tree_atA RNG' A' (k rsp) Q (nret ms1 rsp) mo' mo_'
    /\ sstep_cfg segs ACFG (mkCfg ms1 mo_) evs (SNext (mkCfg (nret ms1 rsp) mo_')).
Proof.
  intros NS R RNG A n k Q ms1 mo mo_ rsp mo' evs Hat Hk Hl Hh Hinv Hsf MR Hst.
  pose proof Hsf as (ACC & Hns & Hk').
  destruct (Hk' rsp mo' evs Hst) as (RNG' & A' & HF & HLE & Hsf').
  pose proof (mrel_ainv RNG A mo mo_ ACC MR) as INV.
  destruct (nsA_sound NS n RNG A ms1 mo mo_ rsp mo' evs Hat Hh Hinv Hns (proj1 ACC) MR INV Hst)
    as (Hh' & Hinv' & mo_' & Hss & MP).
  exists RNG', A', mo_'. split; [|exact Hss].
  split; [apply Hk; exact HF|]. split; [eapply leaves_unreachable_m_step; eassumption|].
  split; [exact Hh'|]. split; [exact Hinv'|]. split; [exact Hsf'|].
  eapply mrel_le; [exact MP| exact HLE].
Qed.

(* [comment removed for export] *)
Lemma ttrace_exists : node_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> exists full, ttrace nstep nexit t mo full.
Proof.
  intros NS R t. induction t as [r|n k IH]; intros RNG A Q ms mo mo_ HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret _ nstep r mo Hl).
  - pose proof HT as (Ht & Hl & Hh & Hinv & Hsf & MR).
    cbn [implF] in Ht.
    pose proof (tree_atA_ainv _ _ _ _ _ _ _ HT) as INV.
    destruct (evtF_lift segs (m_vm_lazy mo) A NMAX RNG _ ms mo_ (proj1 (tsafeA_acct _ _ _ _ Hsf)) INV
                ltac:(rewrite (mrel_halted _ _ _ MR); exact Hh) Ht)
      as (ms1 & mo1_ & CS & [Hat1 Hk1] & INV1 & SB1).
    assert (MR1 : mrel A mo mo1_) by (eapply mrel_after; eauto).
    destruct (nsA_progress NS n RNG A ms1 mo mo1_ Hat1 Hh Hinv (proj1 (proj2 Hsf)) (proj1 (tsafeA_acct _ _ _ _ Hsf)) MR1 INV1)
      as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
    + destruct (tree_atA_step NS RNG A n k Q ms1 mo mo1_ rsp mo' evs Hat1 Hk1 Hl Hh Hinv Hsf MR1 Hst) as (RNG' & A' & mo_' & HT' & _).
      destruct (IH rsp RNG' A' Q (nret ms1 rsp) mo' mo_' HT') as (full' & Hfull').
      exists (evs ++ full'). cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
    + exists [ExitEv code (m_fs mo')]. cbn. left. exists code, mo'. split; [assumption|reflexivity].
Qed.

Lemma ptraces_nonempty : node_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> ptraces t mo [].
Proof.
  intros NS R t RNG A Q ms mo mo_ HT. destruct (ttrace_exists NS t RNG A Q ms mo mo_ HT) as (full & Hf).
  exists full. split; [exact Hf| apply is_prefix_nil].
Qed.

(* [comment removed for export] *)

Lemma cstep_node_ok : forall ms mo ms' mo',
  cstep segs (ms, mo) (ms', mo') ->
  ShapeAlg.node_ok segs (mkCfg ms mo) unit (fun _ => []) (fun _ => mkCfg ms' mo').
Proof.
  intros ms mo ms' mo' (Hh & Hs & Ha). cbn in Hh, Hs, Ha. split.
  - intros _. eapply sstep_cfg_instr; eauto.
  - intros e st Hss. exists tt. inversion Hss; subst; try congruence.
    all: try (rewrite Ha in *; congruence).
    match goal with H : mi_account_step segs ms mo = MachineOk _ |- _ => rewrite Ha in H; inversion H; subst; auto end.
Qed.

Lemma csteps_srealizes : forall ms mo ms' mo' T,
  csteps segs (ms, mo) (ms', mo') ->
  SpinAlg.srealizes segs (mkCfg ms' mo') T -> SpinAlg.srealizes segs (mkCfg ms mo) T.
Proof.
  intros ms mo ms' mo' T CS.
  remember (ms, mo) as c eqn:Ec. remember (ms', mo') as c' eqn:Ec'.
  revert ms mo ms' mo' Ec Ec'. induction CS as [c|c c1 c2 ST CS IH]; intros ms mo ms' mo' -> E2 Hs.
  - inversion E2; subst. exact Hs.
  - destruct c1 as [ms1 mo1]. eapply SpinAlg.srz_silent1; [apply cstep_node_ok; exact ST|].
    eapply IH; eauto.
Qed.

(* [comment removed for export] *)

Section NodeCase.
  Context {R : Type}.
  Variables (n : node) (k : resp -> itree node R) (Q : R -> footprint -> machine_state -> Prop).
  Variables (RNG : footprint) (A : alw) (ms1 : machine_state) (mo mo1_ : Model).
  Hypothesis NS : node_soundA.
  Hypothesis Hat : at_node n RNG ms1.
  Hypothesis Hk : forall rsp RNG', fstep n rsp RNG RNG' -> implF RNG' (k rsp) Q (nret ms1 rsp).
  Hypothesis Hl : leaves_unreachable_m nstep (Vis n k) mo.
  Hypothesis Hh : m_halted mo = None.
  Hypothesis Hinv : minv mo.
  Hypothesis Hsf : tsafeA RNG A (Vis n k) mo.
  Hypothesis MR : mrel A mo mo1_.
  (* [comment removed for export] *)
  Hypothesis IH : forall rsp RNG' A' ms' mo' mo_',
    tree_atA RNG' A' (k rsp) Q ms' mo' mo_' -> SpinAlg.srealizes segs (mkCfg ms' mo_') (ptraces (k rsp) mo').

  Let c1 : config := mkCfg ms1 mo1_.

  (* [comment removed for export] *)
  Definition succ : Type := { ce : config * list event | sstep_cfg segs ACFG c1 (snd ce) (SNext (fst ce)) }.
  Definition s_evs (i : succ) : list event := snd (proj1_sig i).
  Definition s_nx (i : succ) : config := fst (proj1_sig i).

  (* [comment removed for export] *)
  Definition s_T (i : succ) : ShapeAlg.TSet :=
    fun tr =>
      (m_halted (cfg_model (s_nx i)) = None /\
       exists rsp mo', cfg_ms (s_nx i) = nret ms1 rsp /\ nstep n mo rsp mo' (s_evs i) /\
                      mpost A mo' (cfg_model (s_nx i)) /\ ptraces (k rsp) mo' tr)
      \/ (m_halted (cfg_model (s_nx i)) <> None /\ tr = []).

  Lemma INV1 : ainv (m_vm_lazy mo) A NMAX mo1_.
Proof. eapply mrel_ainv; [eapply tsafeA_acct; exact Hsf| exact MR]. Qed.

  Lemma FOK : footprint_ok (m_vm_lazy mo) A RNG.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"; "NodeCase"] "h01Lh11pp;1p;3p;2p;4p;6g00T3j1ETg00Tkj3DTg001^j10Tg002Cj12Tg002aj1CTg00Ggj17Tg000Gj24Tg00Ugj23Tg00VGj25Tg00Vaj36Tg00F3j21Tg00W8j28Tg00WRj19Tg00ESj1BTg00XRj2:Tg00D;j2;Tg00Xoj1<Tg00Yfj1=Tg00C_j2>Tg01;>j4?Tg01F1j6@Tg01A7j3ATp,2moR0#Ep,1AR1p,3RNGR23Dg004o#0#0#0#0#0#0#2#CR3#7R4f0R5,431335p,4NMAXR6'5P1P5O1f1f2563[^13'1'1X04'8%90%B6g00l;':';%<0#='>'1p,1RR6P2P1p,4nodeP6p,1np,1kC?P0p,3HsfE@3Ao"). Qed.

  Lemma NSF : nsafe n mo.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"; "NodeCase"] "p'0h01Ah12A'h21Rh33RNGh44RNG'h53evsh62moh73mo'h83rsph91ti001ti011ki021ni031ri046tsafeAp;1p;2p;3g00Ggj17Tg003Dj23Tg017aR0j24Tg00S;j32Tg00F3j20Tg00W8j21Tg01WPj36Tg01A7j35Tp,5nsafeR1p,1nR2p,2moR3O2R4g01<gR5g00kER6g01AR#7R7p,5nstepR8P2P3f2R9f1R:f0R;O5g00A6R<g004;R=p,5fstepR>P2f5R2p,3RNGR?P:O4p,1AR@/3;g01@@p605611111001RAp,4nodeRB/49RCp-0RD^66]9^0=^3<]2f3?29;P0PBf4RBPDP:g00QfP1P:P9O2P8PBP2P9P:P;O5P>f7P2f;P:O4f:/3;f=f<P:P;f6P2O1PBO5'0'0X1=,1=X4<,1<[^57^76^85'0n200110000021010320102101'0X66X9CX0=X3<X2Ap?1003104p,1RP:P;p,1kP2O1PBO5'0'0X1='1X4<'1[]5]7]8R<A2?@3104<p,3Hsf3635o"). Qed.

  Lemma succ_node_ok : ShapeAlg.node_ok segs c1 succ s_evs s_nx.
Proof.
    split.
    - intros [[c e] Hs]. exact Hs.
    - intros e st Hss.
      destruct (nsA_complete NS n RNG A ms1 mo mo1_ e st Hat Hh Hinv NSF FOK MR INV1 Hss)
        as [(rsp & mo' & mo_' & -> & _) | (code & mo' & mo_' & -> & _)].
      + exists (exist _ (mkCfg (nret ms1 rsp) mo_', e) Hss). split; reflexivity.
      + exists (exist _ (mkCfg ms1 mo_', e) Hss). split; reflexivity.
  Qed.

  Lemma step_tree_atA : forall rsp mo' evs mo_',
    nstep n mo rsp mo' evs -> mpost A mo' mo_' ->
    exists RNG' A', tree_atA RNG' A' (k rsp) Q (nret ms1 rsp) mo' mo_'.
Proof.
    intros rsp mo' evs mo_' Hst MP.
    pose proof Hsf as (ACC & Hns & Hk').
    destruct (Hk' rsp mo' evs Hst) as (RNG' & A' & HF & HLE & Hsf').
    destruct (nsA_sound NS n RNG A ms1 mo mo1_ rsp mo' evs Hat Hh Hinv Hns FOK MR INV1 Hst) as (Hh' & Hinv' & _).
    exists RNG', A'. split; [apply Hk; exact HF|]. split; [eapply leaves_unreachable_m_step; eassumption|].
    split; [exact Hh'|]. split; [exact Hinv'|]. split; [exact Hsf'|]. eapply mrel_le; eauto.
  Qed.

  Lemma succ_srealizes : forall i, SpinAlg.srealizes segs (s_nx i) (s_T i).
Proof.
    intros [[c e] Hss]. unfold s_nx, s_evs, s_T. cbn [proj1_sig fst snd].
    destruct (nsA_complete NS n RNG A ms1 mo mo1_ e (SNext c) Hat Hh Hinv NSF FOK MR INV1 Hss)
      as [(rsp & mo' & mo_' & E & Hst & MP) | (code & mo' & mo_' & E & Hex & -> & Hh')]; inversion E; subst; cbn [cfg_ms cfg_model].
    -
      destruct (step_tree_atA rsp mo' e mo_' Hst MP) as (RNG' & A' & HT').
      pose proof (IH rsp RNG' A' _ _ _ HT') as SR.
      eapply SpinAlg.srz_conseq; [exact SR|].
      assert (Hh0 : m_halted mo_' = None).
      { rewrite (mrel_halted _ _ _ MP). exact (proj1 (proj2 (proj2 HT'))). }
      intros tr. split.
      + intros Htr. left. split; [exact Hh0|]. exists rsp, mo'. split; [reflexivity|]. split; [exact Hst|]. split; [exact MP| exact Htr].
      + intros [(_ & rsp2 & mo2 & Ems & Hst2 & MP2 & Htr) | [Hc _]]; [| exfalso; apply Hc; exact Hh0].
        destruct (step_tree_atA rsp2 mo2 e mo_' Hst2 MP2) as (RNG2 & A2 & HT2).
        rewrite <- Ems in HT2.
        pose proof (IH rsp2 RNG2 A2 _ _ _ HT2) as SR2.
        apply (SpinAlg.srealizes_obs_iff segs _ _ SR tr).
        apply (SpinAlg.srealizes_obs_iff segs _ _ SR2 tr). exact Htr.
    -
      eapply SpinAlg.srz_conseq; [apply SpinAlg.srz_halt; cbn; congruence|].
      intros tr. unfold ShapeAlg.t_nil. split.
      + intros ->. right. split; [cbn; congruence| reflexivity].
      + intros [(Hc & _) | [_ ->]]; [cbn in Hc; congruence| reflexivity].
  Qed.

  Lemma node_shape_eq :
    ShapeAlg.t_eq (ShapeAlg.t_alt (fun i => ShapeAlg.t_emit (s_evs i) (s_T i))) (ptraces (Vis n k) mo).
Proof.
    intros tr. unfold ShapeAlg.t_alt, ShapeAlg.t_emit, ptraces. split.
    - intros ([[c e] Hss] & Hi). unfold s_nx, s_evs, s_T in Hi. cbn [proj1_sig fst snd] in Hi.
      destruct (nsA_complete NS n RNG A ms1 mo mo1_ e (SNext c) Hat Hh Hinv NSF FOK MR INV1 Hss)
        as [(rsp & mo' & mo_' & E & Hst & MP) | (code & mo' & mo_' & E & Hex & -> & Hh')]; inversion E; subst; cbn [cfg_ms cfg_model] in Hi.
      + destruct (step_tree_atA rsp mo' e mo_' Hst MP) as (RNG' & A' & HT').
        destruct Hi as [Hp | (tr' & -> & [(_ & rsp2 & mo2 & Ems & Hst2 & MP2 & (full2 & Hf2 & Hp2)) | [Hc _]])].
        * destruct (ttrace_exists NS (k rsp) RNG' A' Q _ _ _ HT') as (full' & Hf').
          exists (e ++ full'). split; [| eapply is_prefix_trans; [exact Hp| apply is_prefix_app]].
          cbn. right. exists rsp, mo', e, full'. repeat split; assumption.
        * exists (e ++ full2). split; [| apply is_prefix_app_l; exact Hp2].
          cbn. right. exists rsp2, mo2, e, full2. repeat split; assumption.
        * exfalso. apply Hc. cbn [s_nx proj1_sig fst snd cfg_model]. rewrite (mrel_halted _ _ _ MP). exact (proj1 (proj2 (proj2 HT'))).
      + destruct Hi as [Hp | (tr' & -> & [(Hc & _) | [_ ->]])].
        * exists [ExitEv code (m_fs mo')]. split; [| exact Hp]. cbn. left. exists code, mo'. auto.
        * cbn [s_nx proj1_sig fst snd cfg_model] in Hc. congruence.
        * exists [ExitEv code (m_fs mo')]. split. { cbn. left. exists code, mo'. auto. }
          rewrite app_nil_r. apply is_prefix_refl.
    - intros (full & Hf & Hp). cbn in Hf.
      destruct Hf as [(code & mo' & Hex & ->) | (rsp & mo' & evs & tr' & Hst & Hf' & ->)].
      + destruct (nsA_exit NS n RNG A ms1 mo mo1_ code mo' Hat Hh Hinv NSF MR Hex) as (Hh' & mo_' & Hss & Hh_').
        exists (exist _ (mkCfg ms1 mo_', [ExitEv code (m_fs mo')]) Hss). cbn [s_evs s_nx proj1_sig fst snd].
        left. exact Hp.
      + destruct (nsA_sound NS n RNG A ms1 mo mo1_ rsp mo' evs Hat Hh Hinv NSF FOK MR INV1 Hst) as (Hh' & Hinv' & mo_' & Hss & MP).
        exists (exist _ (mkCfg (nret ms1 rsp) mo_', evs) Hss). unfold s_evs, s_nx, s_T. cbn [proj1_sig fst snd cfg_ms cfg_model].
        destruct (ShapeAlg.is_prefix_app_split _ _ _ Hp) as [Hp1 | (tr2 & -> & Hp2)].
        * left. exact Hp1.
        * right. exists tr2. split; [reflexivity|]. left. cbn [s_nx proj1_sig fst snd cfg_model cfg_ms].
          split; [rewrite (mrel_halted _ _ _ MP); exact Hh'|].
          exists rsp, mo'. split; [reflexivity|]. split; [exact Hst|]. split; [exact MP|]. exists tr'. auto.
  Qed.

  Lemma node_srealizes : SpinAlg.srealizes segs c1 (ptraces (Vis n k) mo).
Proof.
    destruct (nsA_progress NS n RNG A ms1 mo mo1_ Hat Hh Hinv NSF FOK MR INV1) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
    - destruct (nsA_sound NS n RNG A ms1 mo mo1_ rsp mo' evs Hat Hh Hinv NSF FOK MR INV1 Hst) as (_ & _ & mo_' & Hss & _).
      eapply SpinAlg.srz_conseq; [| apply node_shape_eq].
      apply (SpinAlg.srz_node segs c1 succ s_evs s_nx s_T (exist _ (mkCfg (nret ms1 rsp) mo_', evs) Hss)
               succ_node_ok succ_srealizes).
    - destruct (nsA_exit NS n RNG A ms1 mo mo1_ code mo' Hat Hh Hinv NSF MR Hex) as (_ & mo_' & Hss & _).
      eapply SpinAlg.srz_conseq; [| apply node_shape_eq].
      apply (SpinAlg.srz_node segs c1 succ s_evs s_nx s_T (exist _ (mkCfg ms1 mo_', [ExitEv code (m_fs mo')]) Hss)
               succ_node_ok succ_srealizes).
  Qed.
End NodeCase.

(* [comment removed for export] *)

Theorem implF_srealizes : node_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> SpinAlg.srealizes segs (mkCfg ms mo_) (ptraces t mo).
Proof.
  intros NS R t. induction t as [r|n k IHk]; intros RNG A Q ms mo mo_ HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret _ nstep r mo Hl).
  - pose proof HT as (Ht & Hl & Hh & Hinv & Hsf & MR).
    cbn [implF] in Ht.
    pose proof (tree_atA_ainv _ _ _ _ _ _ _ HT) as INV.
    destruct (evtF_lift segs (m_vm_lazy mo) A NMAX RNG _ ms mo_ (proj1 (tsafeA_acct _ _ _ _ Hsf)) INV
                ltac:(rewrite (mrel_halted _ _ _ MR); exact Hh) Ht)
      as (ms1 & mo1_ & CS & [Hat1 Hk1] & INV1 & SB1).
    assert (MR1 : mrel A mo mo1_) by (eapply mrel_after; eauto).
    eapply csteps_srealizes; [exact CS|].
    apply (node_srealizes n k Q RNG A ms1 mo mo1_ NS Hat1 Hk1 Hl Hh Hinv Hsf MR1).
    intros rsp RNG' A' ms' mo' mo_' HT'. eapply IHk. exact HT'.
Qed.

(* [comment removed for export] *)
Theorem implF_obs_trace : node_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ ->
  forall tr, obs_trace_cfg segs ACFG (mkCfg ms mo_) tr <-> ptraces t mo tr.
Proof. intros NS R t RNG A Q ms mo mo_ HT. apply SpinAlg.srealizes_obs_iff. eapply implF_srealizes; eauto. Qed.

Theorem implF_no_error : node_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> ~ reaches_error_cfg segs ACFG (mkCfg ms mo_).
Proof. intros NS R t RNG A Q ms mo mo_ HT. eapply SpinAlg.srealizes_no_error. eapply implF_srealizes; eauto. Qed.

Theorem implF_modeled : node_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> ~ reaches_unmodeled_cfg segs ACFG (mkCfg ms mo_).
Proof.
  intros NS R t RNG A Q ms mo mo_ HT Hu. apply (implF_no_error NS t RNG A Q ms mo mo_ HT).
  apply reaches_unmodeled_cfg_reaches_error_cfg. exact Hu.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition epostF {X} (Q : X -> footprint -> machine_state -> Prop) : exc X -> footprint -> machine_state -> Prop :=
  fun r RNG ms => match r with Unr => True | Ok a => Q a RNG ms end.

Lemma implF_ret_unr : forall {X} RNG (Q : X -> footprint -> machine_state -> Prop) ms,
  implF RNG (Ret Unr) (epostF Q) ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "h01Qh13RNGh21Xh32msp;1p;4p;5p;3p;2p102SPp605;1111111111001p102C8p60551111000p8p200R0g0142R1p60551111002p8P0g02XgR2p6051002p8g02Y^j16TP2j45j22Tg02ZVj50Tg02[Oj11Tg019Oj34TP1j53Tg00A6R1f1R2g015\R3p-0[\1[p,4segsf2R1f3R4P2%64R5P1C5f0R6g00R_D0%14R7P1p,4node?4751242P6D3eX33W0W1X20o"). Qed.

Lemma implF_ret_ok : forall {X} RNG (Q : X -> footprint -> machine_state -> Prop) a ms,
  evtF segs RNG (Q a RNG) ms -> implF RNG (Ret (Ok a)) (epostF Q) ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "h01Hh11Qh23RNGh31Xh41ah52msp;4p102SPp605;1111111111001p102C8p60551111000p8p200R0p10142p60551111002p8P0p102Xgp6051002p8g014hj40Tg00A6R1f1R2g015\R3p-0[\1[f2R1p,4segsf3R4P1P2P4O2f0R4C0P4W0X53W4W1W2X30o"). Qed.

Lemma implF_ebind : forall {X Y} RNG (t : itree node (exc X)) (f : X -> itree node (exc Y)) Q1 Q ms,
  implF RNG t (epostF Q1) ms -> (forall a RNG' ms', Q1 a RNG' ms' -> implF RNG' (f a) (epostF Q) ms') ->
  implF RNG (ebind t f) (epostF Q) ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "p'0h04RNG'h13ms'h22H'h31ai001ah41ri011rh52Hfh62Hth71Qh82Q1h93RNGh:1Xh;1Yh<1fh=2msh>1ti021ep;1p;2p;5p;3p;4p;:p102SPp605;1111111111001p102C8p60551111000p8p200R0g0142R1p60551111002R2p8P0g02\GR3p60551111003p8P0g02XgR4p6051002R5p8P0g02]BR6p4p7210p8p201R7P2p8P7P3p605611111002p8P7P5p8P7g02^6R5p60551111001p8P7P6p4p73110p8g02[OR2j10Tg017aj23TP4j21j54TP1j52Tg02Y^j15Tg019Oj36TP5j4:Tg02_4j29TP3l:8TP6j57Tg00A6R6p,4nodeR3f2R5#0'3f3R1%01,33[f4R4g015\R8p-0[\6[R9f7R:#0f5R;P411:5f0R<D2f8R=f6R>P5f1R?P<O3f;R@#0P5P=P1O111@>P?D2[^18^06]3f9RA#0RB%0=RCP:P>P2f:RD%0D,33P<%5A963BP:P<O1n10110100020010100X4B11A411=1R4P5P?P2PDf=RDP=P5P?P<D4%0DREP5P2f>R2%02,33P1%5D963EP@P<O1n1011010002001010011D=P?D2[^18^06P<f<RDP:%5DP?P<D4PDP5P:P?C:W2X18X06P2PA1925P?P<D4P>P1P5P?P<O4W2X18X06X3@P<O1n10110200020010100X4BM:8PCP:P3PAP=P>P;D7P4P5D2eW5W6X=8X79W8W<W>W9X;7X:0o"). Qed.

Lemma implF_epost_mono : forall {X} RNG (t : itree node (exc X)) (Q Q' : X -> footprint -> machine_state -> Prop) ms,
  implF RNG t (epostF Q) ms -> (forall a RNG' ms', Q a RNG' ms' -> Q' a RNG' ms') -> implF RNG t (epostF Q') ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "p'0h04RNG'h13ms'h22H0h31ai001ah41Hh52HQh61Qh72Q'h83RNGh91Xh:2msh;1rh<1ti011ep;1p;2p;5p;8p102SPp605;1111111111001p102C8p60551111000p8p200R0g0142R1p60551111002p8P0g02_lR2p60551111002p8P0g02XgR3p6051002p8g02[OR4j12Tg017aj27TP3j21j50TP1j55Tg02Y^j14Tg02_4j23TP2j86Tg00A6R2p,4nodef1R1#2'7f2R3g015\R5p-0[\2R6[f3R7P6[f5R6#2f4R8P71163f0R9D5f6R:P:P3P1P9O3P:P7P3P1O3[^15^02]3f7R;#2R<P:P611;811;7P3P1P4f8R4f;R8P4P3P1P9D0f<R6P4P7P3P1D0[^15^02P9g00QfP9W2f:R4P;%44P1P9D0P8P;%48P3P1D0[eX15X02f9R8P8P3P1P9O3P:P7P3P1P9O4W2P6P81363P1P9D0f=R6P81367P3P1D0[eX15X02W3P9O1n10110100020010100X;<G6W5W4X:5W7W6W<W8X90o"). Qed.

(* [comment removed for export] *)
Lemma implF_enode : forall {X} RNG n (pl : resp -> option X) (Q : X -> footprint -> machine_state -> Prop) ms,
  evtF segs RNG (fun ms1 => at_node n RNG ms1 /\
                   forall rsp RNG' a, fstep n rsp RNG RNG' -> pl rsp = Some a -> evtF segs RNG' (Q a RNG') (nret ms1 rsp)) ms ->
  implF RNG (enode n pl) (epostF Q) ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ITreeA ()) ["ITreeA"] "p'0h01ai001ah14RNG'h23rsph32Hkh43ms1h51Hh62H0h72HFh83Hath91Qh:3RNGh;1Xh<2msh=1nh>1oi011oh?2pli021xp;1p;2p;3p;4p;5p;7p102SPp605;1111111111001p102C8p60551111000p8p200R0g0142R1p60551111002p8P0g02XgR2p6051002p8P0g02`gR3p4p7210p8g00nbR4j13Tg01egj25Tg006Dj36Tg01<4j20Tg014hj41Tg00F3R5j2;Tg02[Oj12Tg017aj2<Tg02_4j2:Tg019Oj34Tg02Y^j19TP2j27j4ATP1j58Tg00M<j2CTg01Fmj1BTg02ZVj5@Tg00FNj4?Tg01:Ej7>TP3j4=Tg00A6R3p,4nodeR1g01<gR2f3R6#3[g015\R7p-0[\3\6p,4segsR8f4R9p,7at_nodeR:P9f5R;f0R<O3f8R=p,5fstepR>f7R?f2R@P=f1RAO4f:RB#3P?P6O115BA36P8P6P?P@P6O210;9RCC1[[]0^13^22';X47P<C1P8P;P:P;f6RDP<O3REf9RFP>P=P@PFPAO4f;RG#3P=P6O115GA36P8P6P=P@P6O2PCC1[[]0^13^22';X47P>P?PAP=P<O4%2BRHPAP4PB%2GRI,<1P?P@O11:G<941I%9B941Hn1011020002101000017BD106@D8[^13^22,;EX47PAP<P:PDP?P<O3P>PFP@PBPAO4REf<RH#3PFP6O115HA36RIP8P6PFP@P6O2RJPCC1[[^0B^13^22';X47P<O1P5P:PDP?PAO3P8P6PJ10D9C1\I\E^0B^13^22P:P?P=P@O3P>PFPAPBP<O4%2HREPAP4PHf=RI#2RJ,<1PFP@O11:I<941J%9H941En1011020002101000017H=10;@D8[^13^22';P<P:P=PFP6O3P>PHP@PIPAO4f?RE#3PHP6O115EA36P8P6PHP@P6O210F9C1[[^0I^13^22P:PBPGP;O3P>PHPAPIP<O4RB%2ER:PAP4PEf@RJ#2R5,<1PHP@O11:J<9415%9E941:n1011020002101000017EG10=@D8[^13^22PAP6P@PAO2P>f>R:P6PEP@O4fAR5#3P:P9O1155A36P8P9P:P@P9O210G;RGC1[[^0EPIP6O1%3JP4P5fBRCP>P5PDPCP;O4fDRK#3RL15KARM76@P8P?P5P@P?O210:=C1[[]0fCRN#2ROP;P4PN%2KR4,<1PA1:K<9414%9N941On1011020002101000017NE10HDD8]3P<P>PCP?PNPDO4fERH#315H@15HA36P8P=PCP@P=O210EFC1[[^0NP<PAP;1CLMO3P4PD1:KA941417KJ10I?RID8eW3X0CP<O1P>PJP;P5P9O4%3N%BN15NA36P8PDPJP@PDO2PIC1[[^05P8P9PCP:%9CR8P9CAPGg00R_D@%2CR5P9A415817C:PGD8eW3n10110100021010200PAO1b>b3X7BX13X22C?W3W8PAP<O2n2001000000121000000W6X47F>%2DP;P1PDP9P6C=17D@PAD8eW5X<7W9W?W=W:X;0o"). Qed.

End ITreeA.

Arguments mrel A mo mo_ /.
Arguments implF {node} segs at_node fstep {R} RNG t Q ms.
Arguments tsafeA {node} nstep nsafe fstep NMAX {R} RNG A t mo.
Arguments ptraces {node} nstep nexit {R} t mo _.
Arguments tree_atA {node} segs at_node nstep minv nsafe fstep NMAX {R} RNG A t Q ms mo mo_.
Arguments implF_srealizes {node} segs at_node nstep nexit minv nsafe fstep NMAX _ {R} t RNG A Q ms mo mo_ _.
Arguments implF_obs_trace {node} segs at_node nstep nexit minv nsafe fstep NMAX _ {R} t RNG A Q ms mo mo_ _.
Arguments implF_no_error {node} segs at_node nstep nexit minv nsafe fstep NMAX _ {R} t RNG A Q ms mo mo_ _.
