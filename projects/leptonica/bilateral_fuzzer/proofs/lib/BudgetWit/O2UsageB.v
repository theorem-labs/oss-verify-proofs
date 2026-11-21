(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from O2/O2Usage.v (whole file): ref_usage and ref_usage_w restated over the budget carrier rzb; the KReplay name table gains entries for the twinned globals and the proof scripts are repointed at them, otherwise byte for byte. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (model0 started in the vDSO run state; the lemma model0_rd2; the recorded (KReplay) proofs of ref_usage and model0_fs re-proved by tactics after leptonica/pix_orient_fuzzer's text at this binary's addresses). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibTail.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout SymExec RefNodes RefMemcpyLib LibWritev.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import Frame.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2StartupDefs O2ExitBase O2Exit O2MemcpyBase O2Memcpy O2Memchr O2Strnlen O2Startup O2StartupFacts O2MainEntry O2OpenFail_defs O2OpenFail_tail O2OpenFail_tail2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MainEntryN O2Usage_defs O2Usage_tail.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.BudgetWit Require Import Rzb SymDriveB O2Usage_tailB.
Ltac2 kr_t_O2UsageB () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes6option01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesI47Corelib5Lists7ListDef6Forall00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC46Stdlib5Lists4List2hdC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvI59OSSVerify5KrLib2O29O2Startup:main_entry00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Logic3notC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive01C46Stdlib5Lists4List2InC46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib2O2<O2Usage_tail3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O27O2Usage2BLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs7u_logM1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_tail4PRE7C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_tail9PRE7_wordC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib2O2<O2MainEntryN=main_regs_okNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2MainEntryN2ENC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2MainEntryN=main_know_okNC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2MainEntryN8evN_argcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7ArgvEnv5argcNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2MainEntryN5valsNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2MainEntryN3p0NC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2MainEntryN6auxvpNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2MainEntryN4rndNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC69OSSVerify5KrLib6Common9CliDriver9SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:length_appC47Corelib4Init5Peano2ltC59OSSVerify5KrLib2O2<O2MainEntryN9main_strNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib6Common7ArgvEnv7u_argcNC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem<branch_takenK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX;log_below_bC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?mem_denot_aboveC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC46Stdlib9micromega;ZifyClasses3injC69OSSVerify5KrLib6Common9CliDriver9SymDriveX8kimg_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail7vadd_wZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_varC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7LibTail6ed_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX@regs_after_keepsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX:flat_introC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun;carry_afterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O27O2Usage>umemcpy1_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib2O2<O2MainEntryN>main_strN_fitsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Spec9msg_usageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib2O2<O2Usage_tail7us_tailC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O27O2Usage6model0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib2O2<O2Usage_tail8PRE7_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_knB0C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc59OSSVerify5KrLib2O27O2Usage=model0_haltedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O27O2Usage;model0_lazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O27O2Usage:model0_fd2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O27O2Usage9a0s_nonulC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs5STOPSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs6u_scrAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2MainEntryN8sr_mainNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2MainEntryN8kn_mainNC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O27O2Usage6hd_nthC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_tail8pre7_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2Usage_defs5u_knAC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?callee_kept_no0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O27O2Usage9model0_fsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O27O2Usage9ref_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib9BudgetWit=O2Usage_tailB3ENVc59OSSVerify5KrLib9BudgetWit8O2UsageB2BLC59OSSVerify5KrLib9BudgetWit=O2Usage_tailB4PRE7C59OSSVerify5KrLib9BudgetWit=O2Usage_tailB9PRE7_wordc59OSSVerify5KrLib9BudgetWit8O2UsageB>umemcpy1_denotC59OSSVerify5KrLib9BudgetWit3Rzb:rzb_mstepsI59OSSVerify5KrLib9BudgetWit3Rzb3rzb00C59OSSVerify5KrLib9BudgetWit=O2Usage_tailB7us_tailC59OSSVerify5KrLib9BudgetWit9SymDriveB7rzb_runc59OSSVerify5KrLib9BudgetWit8O2UsageB6model0C59OSSVerify5KrLib9BudgetWit=O2Usage_tailB8PRE7_lenc59OSSVerify5KrLib9BudgetWit8O2UsageB=model0_haltedc59OSSVerify5KrLib9BudgetWit8O2UsageB;model0_lazyc59OSSVerify5KrLib9BudgetWit8O2UsageB:model0_fd2c59OSSVerify5KrLib9BudgetWit8O2UsageB9a0s_nonulc59OSSVerify5KrLib9BudgetWit8O2UsageB6hd_nthC59OSSVerify5KrLib9BudgetWit=O2Usage_tailB8pre7_imgc59OSSVerify5KrLib9BudgetWit8O2UsageB9model0_fsc59OSSVerify5KrLib9BudgetWit8O2UsageB9ref_usage".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Usage.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  (* [comment removed for export] *)
  Variable lim : Z.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv tid regs0 mem0.
  Hypothesis Hfits : entry_stack_fits sp0 av envv.   (* [comment removed for export] *)

  Definition BL : list (list byte) := [[]; []; guard_bytes a_draw].   (* [comment removed for export] *)
  Hypothesis Hargc : length av <> 2%nat.

  Definition model0 : Model :=
    with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso a_draw)) (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputC av envv fs0 stdin0))).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Lemma model0_halted : m_halted model0 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_O2UsageB ()) ["Usage"] "p;1p;2g0000j10Tg000Uj15Tg0013j12Tg001Vj11Tg0028j14Tg002Zj23Tg0034#0#0#0#0#0#0#5#2R0#1%40'3o"). Qed.
  Lemma model0_lazy : m_vm_lazy model0 = [].
Proof.
ltac2:(KReplay.run1 (kr_t_O2UsageB ()) ["Usage"] "p;1p;2g0000j10Tg000Uj16Tg0013j12Tg003Yj21Tg0049j15Tg004Yj14Tg002Zj23Tg0034#0#0#0#0#0#0#6#2R0/10R0#5%40'3o"). Qed.
  Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof.
ltac2:(KReplay.run1 (kr_t_O2UsageB ()) ["Usage"] "p;1p;2p10059p4p70p1005gp4p710p8g001Vj17Tg0000j10Tg000Uj12Tg006Cj11Tg006aj26Tg007Gj15Tg008?j23Tg002Zj24Tg008aR0#7g0034#0R1#0#0#0#0#0#2%11'6#5,30'4o"). Qed.
  Lemma model0_rd2 : m_channel_reader model0 = true. Proof. exact a_reader. Qed.
  Lemma model0_fs : m_fs model0 = fs0.
Proof. reflexivity. Qed.

  Lemma a0s_nonul : ~ In (Z_to_bv 8 0) (hd [] av).
Proof.
ltac2:(KReplay.run1 (kr_t_O2UsageB ()) ["Usage"] "p'0h01Hh12H0h21li001lh31xi011xh42H1h52Hnh62H2h75Hargch85Hfitsh93Hvah:2MEh;1ah<1eh=2H3h>2Hah?4__p1h@1yhA6Hargc0hB2_HhC3_H0hD3_H1hE3_H2hF7__arithhG4__ffhH6__sat2hI6__sat3hJ8__varmaphK5__withL3a0shM4cstrhN4resthO1vp;1p;2p;3p;7p;<p;4p;6p;8g006Cj1<Tg0000j1;Tg000Uj1TTg0013j1lTg0049R0j1BTg009Yj28Tg00:9R1j17Tg00:YR2j22Tg00;5R3j2=Tg00;Pj1STg00<LR4j36Tg006aj2kTg00<mj1eTg00>1j30j1FTg00>Kj2[Tg00??j2ZTg004Yj1CTg00?Vj3:Tg00?mj1?Tg00@dj7ATg00Abj3@Tg00B_j1HTg00C>j1>Tg00CWj1WTg002Zj29Tg00D5l<GTg00DZj4ETg00EAj2RTg00Edj3QTg00FAj3NTg00Fjj1OTg00GOj2PTg00H7j2DTg00HSj2MTg00I0j3UTg00ITj1jTg00J2j1iTg00JPj1hTg00K;j2LTg00K^j4gTg00LIj7fTg0028j1dTg00Lmj6cTg00MQj8`Tg00N5j2]Tg00NWj2\Tg00OCj3^Tg00Obj4_Tg00PTj31Tg005gj6aTg00Q4j2bTg00QSj6JTg00R0j6KTg00RNj1ITg00S3j3YTg00SJl<XTf0R5#;#;p=4%I5#Ip=5f2R6f1R7;Y5#>p=3g00SoR8g00TNR9P9P9P1P1f3R:P6P7g00TlR;g00UKR<P5M<Xp=Vp,3HvaR=g0034R>#<R?%;>R@#4RA#TRB#lRC#BRDp,2avRE'8#7RF'2RG%;A#4#4#4RA#<,2FRF'=RH%SE%;A#4#4#4#4#4#<'2RA18C5#7%5>#5#5#5#5#5#5#5#<'2X;D=6DER>1kB<RB=3C5X;DRI=6DERJg00UiRKg00VYRL%e5g00W9RM30g00WY,[5=0LM'=X;K1ZDE36RK'=RM'=RN'=RO'=P3PHPO%CCRP=:DE93CBRQP5P3PGPFPQ\OP5P3PAPNPQP5P3P>PMPQP5P3PJPKPQP5PE%BDREP0PD%?5p,3AMBRQp,3sp0R3P7p,4envvRRp,3tidRSp,5regs0RTp,4mem0RUFAA@36R18D:%H;#HRV508#>f4RW,8D#7,2?f5RX96DIf6RY9:DP93CB]5]4]7]8]:]9P5%CDRZ#?PQP3PZPRPSPTPUFAA@3ZR18DZR[=08VR\#>R]%7[R^,2?A6DIZ%7;R;,2?12?<R_P9P9P2P5X39R`P21275#WX@9X39P?P?199?P;P`P<O1P`P`%75R`,99X38199<CVM<GP7CEP_P]%<@R]909^R;#>R2P8P9%F8P1%F9%77=09`A08751R753QX@8X38P[P^199^PVP]199]M<G9N\;P:CEP2%O[12<^%5@#;#<R@,P]1D<]12<@1M]@R^,D<[[12<]R[g00XZR2AU]@7UW>12<^\2^>[p-0R[g00Y6R^#C%B^%j9%i9%h9R^g00YbR@g00ZAR]P]g00ZaR;P^P@P]P]P;P91L9?g00[A1L9<Cgg00[hFf%d]P^P@P]P]P;P6EcG`1]^;P5P6g00\HR;,9L1\56=0L;dA^9<7C_bGbJbKW?P7\_^?[P5A:DPZ93CBPXO2bFbHbIbMbAb1W5W4W7W8W:W9A1D75#?PQP3A1D67PRPSPTPUFAA1D:6RU=@3RA1DW:RR,8D=08V#>A1DXWRV,8D#7,2?A1DYXR?96DIP4PDPIf9R4f8R851DR390E7f:RT=1D49:DP93CBRS[P5f7RQ=1DYR_90EZA1D8QR<90EZPEPZP0PDP[P5P2g00\hR2n10110000020020000000X<Eg00]EP3P5EaP21bS5b1W0P5O1W0A3CB7RSA6DI7R2f?R[f>51D90EUf@RU=1D[90ERPEPEP0PDPEP5PXP5n10110000020020100100X<EPVfARV=1DUP5EJA0EWUPEPDP0PDPDP5PQP7n10110000020020100100X<EP?fBR?=1DVP7EJA0DY?fC90DQP5fDRQ90D8PDfER?A0E4?R?f;96DIfIRYfHRV51D9:DP93CB]1^0S[X2DA0E8QP5P?PEfFA3CBVfJ=1DY9:DP93CB^12]0X2EfGR293CBA6DI2P7W=W6PTP5EKb=W1P4P5EKb1W0P5O1b0P5O1b0W6P5P6P7O3W6W1W0X2EX3DP:P6P7P5O4n200210000000020041101100000000A0E5<A:DP393CB[X2EP_O1P519E<O1b0W5W4W7W8W:W9XNEXLDP7P5O2n10110000020121100100P=p,2MEp,5Hfitsp,5HargcP[P6O6b2XEKX5JP7P5O2n2001000000121000000X0MXD>P7P5O2n2001000000121000000X0NXCAP7P5O2n2001000000121000000X0OXBFX4GP7P5O2n2001000000121000000X0HP7P5O2n2001000000121000000bOo"). Qed.

  Lemma hd_nth : hd [] av = nth 0 av [].
Proof.
ltac2:(KReplay.run1 (kr_t_O2UsageB ()) ["Usage"] "p'0h05Hargch15Hfitsh23Hvah32MEh41li001lh52l0p;1p;7p;3p;2p;4g0000j18Tg000Uj1?Tg0013j1>Tg0049R0j1:Tg00?mj14Tg00@dj76Tg00Abj35Tg009Yj23Tg00B_j1;Tg00>1j31Tg00C>j12Tg004Yj19Tg00?Vj3=Tg00]aj47Tg002Zj2<Tg00PTj30Tp,2avg0034#8#8#8#?#>R1#:R2#:R3P0P2f0R0#4p,3AMBR4p,3sp0R5f1R6p,4envvR7p,3tidR8p,5regs0R9p,4mem0R:F6f2R;=557g00SoR<f3R=,32g00TlR>#;#;R?31#2%91R1f4R@5=2P2P>P@P1C7512]0]1]3]2P0%92RA#4P4P5PAP7P8P9P:F6A55A7132A=1<?#2P2P>PAP1C7,<2W0W1W3W2A0260#4P4P5A02;6P7P8P9P:F6A02=;=557A02@=,32=1<?#2P2P>f5=02@P1C7,<2W0W1W3W2X53X42P6P0O2n10110000020020100100p,3Hvap,2MEp,5Hfitsp,5HargcO4b4o"). Qed.

  (* [comment removed for export] *)
  Lemma umemcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M u_logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE7.
Proof.
ltac2:(KReplay.run1 (kr_t_O2UsageB ()) ["Usage"] "h01Hh12H0h21Mh32P0h41bh51lh64valsp;1p;2p;3p;6g0000j10Tg000Uj1ATg0013j1?Tg0049j1GTg001Vj1STg00^=j2BTg00>1j35Tg006Cj19Tg00_Aj2<Tg00:Yj2FTg00B_j14Tg006aj2:Tg00_kj2ETg03JJj2DTg00akj3CTg00c=j2RTg00cZj36Tg00dTj1QTg00e2j2@Tg002Zj2PTg00R0j6OTg00eOj1NTg00fXj2LTg00gbj1KTg00hkj2>Tg00j4j1JTg00k<j1ITg00lEj2MTg005gj6HTg00RNj1;Tf0R0#0#0p=8%;0#;p=1%;0#0p=7%00#0#0#0p==%00#0#0#0#0#0#0#0p=3%00#;p=2g0034R1#0#8R2#0#8R3#AR4#?R5#G%A2#?R6#S\5R7f1g00TlR8'Bp,3sp0R9555p,4SPlo%11#1#1#1#1#1#1#7#8#=#3#3#3#91<49R1'Fp,4SPhi%03R3#3#3#3#3#3#9,F1%G6R6%48#4#4#4#4#4#4R:%13#7#7#2#7#2#2#2#7#2#1#2#7#8#2#2#1#8#1#2#1#2#2#9R3,:4'ER;g03K8R<f5'Df4R=g00n@R>3C%12#=R2#9,R1,:4R1=6=0557X56P5P91<40%Q2R2'@,:4=6=;A6=1;557X45f3R5?61;R1,P71B=8f2EO1D<=R=%N8/L2R2#K'>,<4%J2'@,:4%I3,>=,E:R:565=571e1M=2=65:=571eAC=5>=571eg03K`g03LOEHb1b0W3W2W6o"). Qed.

  Lemma pre7_len_w : length (word_to_le_bytes 7 (Z_to_bv 64 9071406455288693)) = 7%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_O2UsageB ()) ["Usage"] "p;1p;2g00B_j11Tg000Uj1:Tg0000j12Tg006Cj19Tg006aj28Tg0113j27Tg00RNj16Tf0R0#2#2p=5%60#6p=4%60#2p=3%20#6p=0g00Tl#1#1#1#1#1#1#1g0034#5#5#5R0#:%20#4#3#3#0#3#0#0#0#3#0#4#0#3#5#0#0#4#5#4#0#4#0#0#9'8'7o"). Qed.

  Theorem ref_usage :
    rzb RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x17618) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_usage (hd [] av)) fs0).
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
    assert (HR : regs_ok (EN sp0 av envv tid regs0) sr_mainN regs0) by (eapply main_regs_okN; eassumption).
    assert (HK : know_ok RSEGS (EN sp0 av envv tid regs0) mem0 kn_mainN) by (eapply main_know_okN; eassumption).
    assert (Hac : ev (EN sp0 av envv tid regs0) 16 = argcN (inpA av envv)) by (eapply evN_argc; eassumption).
    change (EN sp0 av envv tid regs0) with (ENV BL (valsN sp0 av envv tid regs0)) in HR, HK, Hac.
    set (vals := valsN sp0 av envv tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold valsN; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0N av envv) by reflexivity.
    cbn [ev ENV] in Hac.
    assert (STR := fun k Hk => main_strN sp0 av envv tid regs0 mem0 Hva Hve Hvsp ME k Hk) || idtac.
    edestruct (main_strN sp0 av envv tid regs0 mem0) as (Sr & Slo & Shi & Slen & t8 & Ht8); try eassumption.
    1:{ instantiate (1 := 0%nat). lia. }
    rewrite <- hd_nth in Sr, Slen, Ht8. set (a0s := hd [] av) in *.
    pose proof (u64_range (cat_argv_ptr (ed_top a_draw) av envv a_execfn 0)) as Hppr.
    clearbody vals.
    pose proof model0_halted as Hh.
    (* [comment removed for export] *)
    run_blk_keep_b u_scrA 38%nat.
    { unfold sc_denot. cbn [branch_taken edenot ev ENV]. rewrite Hac.
      unfold bv_eqb. rewrite (u_argcN (inpA av envv) Hva). change (length (in_argv (inpA av envv))) with (length av).
      change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
      apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    assert (Habove : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV BL vals) mem0 _ 0%nat 0x6b000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    clear EQM.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x10bcd) 7 = Some PRE7).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ u_knA ltac:(let i := kidx u_knA (is_kimg_cov 0x10bcd 7) in exact i)
                 _ _ 0x10bcd 7 HK eq_refl) by (cbn; lia). apply pre7_img. }
    assert (Hdst : store_ok RSEGS M dst 7 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ u_knA ltac:(let i := kidx u_knA (is_kwr_cov (EVar 0) (-560) 7) in exact i)
                    _ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x10bcd) 7 PRE7).
    { constructor; subst dst; rewrite ?u_small by lia; rewrite ?PRE7_len; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- rzb _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x31d38 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10bcd) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x10bcd) 7 _ (seg_rom RSEGS) MC Rc (0x31d38 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 223832) with (0x36a58 : word) by (apply bv_eq; reflexivity).
    eapply rzb_msteps; [exact Hh | exact model0_lazy | exact Hms |]. clear Hms.
    replace (0x31d38 : word) with (Z_to_bv 64 0x31d38) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst PRE7) u_knB0).
    { subst dst. rewrite <- (umemcpy1_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M u_logM1 u_knA [] u_knB0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat u_logM1]. split; [lia|]. split; [|exact I].
      apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst PRE7) u_knB0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 70%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q1 : vals_ev vals1 1 = p0N av envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    rewrite <- model0_fs.
    pose proof (main_strN_fits sp0 av envv tid regs0 mem0 Hva Hve Hvsp ME 0%nat ltac:(lia) Hfits) as Hfit0. rewrite <- hd_nth in Hfit0.
    eapply (O2Usage_tailB.us_tail sp0 BL model0 Hvsp model0_halted model0_lazy model0_fd2 model0_rd2 a0s (p0N av envv) t8 vals1); try eassumption.
    - apply a0s_nonul.
    - unfold p0N. lia.
    - unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.

  Corollary ref_usage_w :
    rzb RSEGS (mkCfg (mkst regs0 (0x17618 : word) mem0 (seg_rom RSEGS)) model0)
               (t_die (msg_usage (hd [] av)) fs0).
Proof.
ltac2:(KReplay.run1 (kr_t_O2UsageB ()) ["Usage"] "h01Hh12b1h22b2h31nh41bp;1p;3p;2p;5p;6g0013j12Tg00>1j33Tg00_Aj24Tg025]j37Tg0000j11Tg000Uj16Tg00RNj10Tg006Cj1<Tg006aj2;Tg028aj38Tg002Zj29Tg01GAj1:Tg02ZEj5ETg02[>j2DTg0049j1CTg004Yj1@Tg00?Vj3?Tg02\3j1>Tg02]7j2=Tg03Nbj3ATg005gj6BTf0R0#1#1p=5g03D`R1%20R2f1R3#2R4g00;5f2R5#2?330g00TNR6f3R7/45147333R8[14531450536%27?353[R9f4#2?375\8A7530P0n2001000000120000000W2W1W3P9^24^12^31P0g0034R1#1#5R2#1#5#6R4%11#0#0#0#1#0#0#5#5#0#0#1#5#<R1,;4R9g00]E9841R11441,96O4b0%24R4P1P4e739P4P9g02fBR9g02i1p,5regs0P0p,4mem0%:9DEg03Ph'D%62#2R2#C%@2p,2av3?#>p,3fs0'=3AX44g03WXP1P0EBb0o"). Qed.

End Usage.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
