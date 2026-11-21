(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO and vvar pages; recorded (KReplay) proofs re-proved by tactics, as pix_orient_fuzzer's copy). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymCall.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib SpecConsts
  SymExec RefNodes RefNodesFS PureModel RefMemcpyLib Hoare MemSplit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Startup V2MainEntry V2OpenFail_defs V2OpenFail V2Open_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Open () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes6option01I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c59OSSVerify5KrLib2V26V2Open4fds0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open3vm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2OpenFail6model0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open6model0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open5fds1gC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00c59OSSVerify5KrLib2V26V2Open7model1gC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01c59OSSVerify5KrLib2V26V2Open7out_winC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3subc59OSSVerify5KrLib2V26V2Open9above_sp0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalK47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathK47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib2V26V2Open9at_mallocC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry2p1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open3ENVC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open7m1_pureC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9PureModel9mp_haltedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCallAmem_denot_out_winC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Open_defs6STOPS2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2Open_defs6o_srB0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2?V2OpenFail_defs3knAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib2V2?V2OpenFail_defs3srAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5ldiffC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic3and01C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8AT_FDCWDC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBopen_ignored_flagsI47Corelib7Numbers7BinNums1N00C47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib2V2;V2MainEntry8main_strC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib4Init3Nat3addC59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC59OSSVerify5KrLib6Common8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State8alloc_fdC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsc59OSSVerify5KrLib2V26V2Open?open_err_branchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2OpenFail3ENVC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open;openat_regsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr03C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_regsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7add_0_rC69OSSVerify5KrLib6Common9CliDriver8SymDrive;regs_set_a0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive:v_addi_pc4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open>open_ok_blockBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open=alloc_fd_initC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open?model1_with_fdsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2OpenFail9of_blockAC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06C56Stdlib6ZArith4Znat5Nat2Z7inj_addC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosc59OSSVerify5KrLib2V26V2Open:path_factsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib2V26V2Open6m0_fdsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open9model0_OFC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupI47Corelib4Init5Peano2le00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC59OSSVerify5KrLib6Common7FileSim@read_cstr_of_rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2OpenFail:path_plainC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupc59OSSVerify5KrLib2V26V2Open@fd_lookup_init_3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2OpenAopen_pipeline_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:RefNodesFSArz_openat_file_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open7m0_pureC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?is_ecall_ECALLWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec8dot_pathC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open:path_nonulC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V26V2Open5m0_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FileSim3mrbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9read_cstrK4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result01C59OSSVerify5KrLib6Common:RefNodesFS@rz_openat_dir_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8dot_pathI4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result00".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS2 scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS2 scr NX true.

Lemma alloc_fd_init : forall e0 e1 e2,
  alloc_fd [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] = Z_to_bv 64 3.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) [] "h02e0h12e1h22e2p;1p;2p-1R0p10000p4p710p8P0p1000Gp4p710p8p1000gp4p70R0p1001Wp4p710R1p8P0p10023p4p710R0p8p1002Qp4p70R2P1p8P2P0p8p1003?p4p70R2P1p8P2P0p8g0045j10Tg004Zj16Tg0058j12Tg005[j11Tg006@j15Tg006^j24Tg007Dj23Tg007^R0g008VR2#0#0#0#0#0#0#6R1#2%12#5,41'3X20X10W0o"). Qed.
Lemma fd_lookup_init_3 : forall e0 e1 e2,
  fd_lookup [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] (Z_to_bv 64 3) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) [] "h02e0h12e1h22e2p;1p;2g009;j12Tg009]j11Tg007Dj20Tg007^R0%20%10'0X20X10W0o"). Qed.

Section Open.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable lim : Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).

  (* [comment removed for export] *)
  Definition fds0 : list (word * FdEntry) :=
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
     (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  Definition vm0 : VmMaps := mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 a_kernel) [] [] brk brk lim mbase sp0.
  Definition model0 : Model :=
    with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso a_draw)) (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputC [a0s; path] envv fs0 stdin0))).
  (* [comment removed for export] *)
  Definition fds1g (fd3 : FdEntry) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition model1g (fd3 : FdEntry) : Model := mkModelC (fds1g fd3) vm0 stdin0 fs0 None (Some tid) None.

  Lemma model0_eq : model0 = mkModelC fds0 vm0 stdin0 fs0 None (Some tid) None.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "p;1p;2p;8g0045j10Tg004Zj13Tg0058j12Tg009]j11Tg00:?j27Tg00:aj16Tg00;Aj85Tg007Dj24Tg00<Cp,3AMBg00=9g00=lp,6stdin0p,3fs0g008V#0#0#0R0#0#0#0#3#2R1#1p,3tid,71%30#2#6#1G5'4o"). Qed.
  Lemma model0_OF : model0 = V2OpenFail.model0 sp0 a0s path envv tid brk mbase fs0 stdin0 lim.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "p;;p;2g00>^l;1Tg007Dj20Tg00<Cp,3AMBp,3sp0p,3a0sp,4pathp,4envvp,3tidp,3brkp,5mbasep,3fs0p,6stdin0p,3limM;1'0o"). Qed.
  Lemma m0_fds : m_fds model0 = fds0.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "p;1p;2g0045j10Tg004Zj15Tg0058j12Tg00?Wj21Tg00:aj14Tg007Dj23Tg008V#0#0#0#0#0#0#5#2g007^'1#4g00=9'3o"). Qed.
  Lemma m0_fs : m_fs model0 = fs0.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "p;2g007Dj20Tg002Qp,3fs0'0o"). Qed.
  Lemma m0_pure : md_pure model0.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "p;1p;2p;4g0045j10Tg004Zj19Tg0058j15Tg009;j14Tg009]j18Tg007Dj21Tg00?Wj27Tg00:aj12Tg00@7j13Tg00@Wj46Tg00AVg008V#0#0#0#0#0#0#9#5R0#4%80'11700R1#2%31'1%20%30'1C6o"). Qed.
  Lemma m1_fds : forall fd3, m_fds (model1g fd3) = fds1g fd3.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "h03fd3p;1p;2g0045j10Tg004Zj16Tg0058j12Tg00?Wj21Tg00:aj15Tg00BKj14Tg007Dj23Tg007^R0g008V#0#0#0#0#0#0#6#2/10#5f0#4'3W0o"). Qed.
  Lemma m1_fs : forall fd3, m_fs (model1g fd3) = fs0.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "h03fd3p;2g007Dj20Tg007^g002Qp,3fs0'0W0o"). Qed.
  Lemma m1_vmmaps : forall fd3, m_vmmaps (model1g fd3) = vm0.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "h03fd3p;2g007Dj20Tg007^g00C?g00=l'0W0o"). Qed.
  Lemma m1_pure : forall fd3, md_pure (model1g fd3).
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "h03fd3p;1p;2p;4g00D6j1:Tg0045j10Tg004Zj16Tg0058j14Tg009;j19Tg009]j18Tg007Dj21Tg00?Wj25Tg00:aj12Tg00@7j13Tg00@Wj47Tg007^f0#:g008V#0#0#0#0#0#0#6#4R0#9%80'11500R1#2%31'1%20%30'1C7W0o"). Qed.
  Lemma fds1_2 : forall fd3, fd_lookup (fds1g fd3) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "h03fd3p;1p;2g009;j17Tg0045j10Tg004Zj12Tg006@j11Tg006^j26Tg00Dlj15Tg00:?j23Tg007Dj24Tg007^R0%70g008V#0R1#0#0#0#0#0#2%11'6#5,30'4W0o"). Qed.
  Lemma fds1_3 : forall fd3, fd_lookup (fds1g fd3) (Z_to_bv 64 3) = Some fd3.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "h03fd3p;1p;2g009;j12Tg00:?j21Tg007Dj20Tg007^R0%20f0,10'0W0o"). Qed.
  Lemma model1_with_fds : forall fd3,
    with_fds (fd_insert (m_fds model0) (alloc_fd (m_fds model0)) fd3) model0 = model1g fd3.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "h03fd3p;1p;2g00D6j11Tg007Dj20Tg007^g00<Cf0#1'0W0o"). Qed.

  (* [comment removed for export] *)
  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.
  (* [comment removed for export] *)
  Definition out_win (M : word -> option byte) : Prop :=
    forall a : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned a < bv_unsigned sp0)%Z -> M a = mem0 a.
  Lemma out_win_above : forall M, out_win M -> above_sp0 M.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "h02Hah14__p1h24__x1h34__x2h41Hh51Mh67__arithh74__ffh86__sat1h96__sat2h:8__varmaph;5__with<1ap;1p;2p;3p;4p;6p;7p;8g0045j12Tg004Zj17Tg0058j1;Tg009;j1VTg00Edj1LTg00FZj23Tg00GDj21Tg006@j14Tg005[j19Tg00G`j2?Tg00HHj25Tg00Hdj2<Tg00IAj3UTg00@7j1TTg00:aj1STg00Iej2KTg00JCj1HTg00Jaj4ETg00K?j1DTg00K]j1CTg00LHj2:Tg00Lkj48Tg009]j1BTg00MVj6ATg00N:j7FTg00N^j6GTg00OBj8@Tg00Ofj2ITg007Dj2JTg00PHj2>Tg00Q4j3MTg00QNj3NTg00Qmj4=Tg00R_j2OTg00S:j2PTg00SWj1QTg00TOj7RTf0R0#2#2p=0f1R1g00U3R2g00URR3P3g00V2R4P0g00VRFRp=6g008VR5#2R6#0R7#2#0R8#7R9#;R:%77#;#V[%L0p,3sp0,39R71390'1f2R;P1%46R<%96#9#2#4R='?g00W2R>/5<11>=1<<=R?,5>[[11><R@g00WPRAAU<=1UW011>?\A^0@p-0R@g00WlRAg00XJR?#T%S?PA1KA;P1%HACE%DA%CAR?P2P3P3P4PA1:A5R5g00Y61:A6R6C8,6?%B3P?P2P3P3P4P?P2P3P3P4P?P2P3P3P4f4R3EAPAP6g00Y]P5C8,6?FFEGG@1I?4P0P;g00ZDR?g00ZdR4'J1>0;=M?4dANA>1C=b7b:b;X2AW3W11101f3R>15;1'Og00[D[[^2A^3A^1@P0%28#0#0#0#0#0#0#0#0#4,P71393R3'1P3P7P>O4b6b8b9O2W0X<:%Q1eW4W5o"). Qed.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "p'0h01Hh12H0h21li001lh32H1h42Hlh52Hxh61ah71eh82H2h91xi011xh:2Hnh;2_Hh<3_H0h=3_H1h>3_H2h?1vp;1p;3p;2p;6g006@j1<Tg0045j16Tg004Zj1DTg0058j1KTg00:aR0j1BTg00@7j1HTg00[aj34Tg000Gj2>Tg00\Aj1=Tg00GDj27Tg00R_R1j25Tg00\aj1CTg00]]R2j33Tg006^j2JTg00^>j3:Tg00^Uj1;Tg00^nj1ITg00Q4j30Tg00`2j2GTg00`fj2FTg001Wj6?Tg00a=j2ETg00a\j68Tg0023j69Tg007Dj2@Tg005[j1ATf0R3#6#6p=1%A3#Ap=2p,3Hvag008VR4#<%64#1R5#DR6#KR7#BR8p,3a0sR9p,4pathR:%H8R;548R<548R='>#=R>'7%65#1#1#1R5#<,7>'5R>%C=%65#1#1#1#1#1#<'7R51>73#=%24#2#2#2#2#2#2#2#<'7X68=38=R4g00W2,J6R6=:73#;X68R?=38=R@g000gRAg00ZDRB%I3g00b9RC30g00bY,G3=0BC'5X6A1F8=33RA'5RC'5RB'5RD'5P1P>PDA:76:#;REP3P1P5PBPEP3P1P4PCPEP3P1P@PAPEP3P2P8P?%B8R1f1RF;0=PE[PFA01;=RGP1P;P0P8p-0P3g00WPg00[DRHn10110000020020000000X71RIg00cZRJP=P3E?PH1EE3RKb1X0GP3O1W0A:76F#;RGA38?FRLf3RMf2RN548RO=01=f4RP=48MRQ=01=P1P1P0P8P1P3f5RRP3n10110000020020100100X71RSA48RPRTP=P3E8A01P<P1P8P0P8P8P3f7R0PFn10110000020020100100X71RUf6RV=48RRRP=PFE8A08V9A0809P3f8RW=089P8P9f9RX=01<RYf;938?RZPE]4^5G[X28A01W<P3PYP1P<A:769#;R6PE^4L]5X21A38?<P2P8P?A01F<PE[P3A01;<R2P1P;PIPJP<P3E?PHPKb1X02P3O1W0A01O<A01Q<P1P1PSPTP<P3E8A01P;P1P8PUPRP<PFE8A08V:A080:P3A08W:P8P:A01X;R:PE^1Z^0G[X28A01W;P3P:P1P;PE^1L^0EX21A38?;PFW8X3Ef:R?P3E9b8W1PXP3E9b1W0P3O1b0P3O1b0W3P3PNPFO3W3X1LX0GX21X98PMPNPFP3O4n200210000000020041101100000000A013<PE[X21P<O1P31@1<O1b0W4X56P?P3E9b3W1PXP3E9b1W0P3O1b1P3O1b1W0P3PNPFO3W0W4W5X21X98PMPNPFP3O4n200210000000020141101100000000A013=PE[X21P=O1P31@1=O1b0X>AX:@PFP3O2n2001000000121000000X0CX=4PFP3O2n2001000000121000000X0BX<5PFP3O2n2011000000121000000X0DX;>PFP3O2n2011000000121000000b?o"). Qed.

  (* [comment removed for export] *)
  Definition open_err_branch (KA : TSet) : Prop :=
    forall e vals R M,
      In e openat_errnos ->
      length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
      vals_ev vals 1 = p0 a0s path envv -> vals_ev vals 2 = p1 a0s path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
      above_sp0 M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x43d68) M (seg_rom RSEGS)) model0) KA.

  (* [comment removed for export] *)
  Definition at_malloc (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 38%nat -> vals_ev vals 0 = sp0 ->
      vals_ev vals 1 = p0 a0s path envv -> vals_ev vals 2 = p1 a0s path envv -> vals_ev vals 5 = tid ->
      regs_ok (ENV vals) o_srB R -> know_ok RSEGS (ENV vals) M o_knB ->
      out_win M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x3c370) M (seg_rom RSEGS)) (model1g fd3)) KB.

  (* [comment removed for export] *)
  Lemma open_ok_blockB : forall fd3 KB vals R M,
    at_malloc fd3 KB ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 ->
    vals_ev vals 1 = p0 a0s path envv -> vals_ev vals 2 = p1 a0s path envv -> vals_ev vals 5 = tid ->
    regs_ok (ENV vals) (sr_upd srA (ridx 10) (ELit 3)) R -> know_ok RSEGS (ENV vals) M knA ->
    out_win M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x43d68) M (seg_rom RSEGS)) (model1g fd3)) KB.
  Proof.
    intros fd3 KB vals R M HKB HL P0 P1 P2 P5 HR HK HA.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (mp_halted _ (m1_pure fd3)) as Hh.
    change (sr_upd srA (ridx 10) (ELit 3)) with o_srB0 in HR.
    run_block_keep scr0 38%nat.
    apply (HKB vals); try assumption.
    intros x Hx. rewrite EQM. rewrite (mem_denot_out_win (ENV vals) M _ 0%nat);
      [apply HA; exact Hx | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; unfold WIN; exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma openat_regs : forall vals R,
    vals_ev vals 2 = p1 a0s path envv -> regs_ok (ENV vals) srA R ->
    bv_unsigned (getr R 17) = 56%Z /\ getr R 10 = AT_FDCWD /\ getr R 11 = p1 a0s path envv
    /\ Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Open ()) ["Open"] "h01bh12b1h22b2h31nh41Hh52HRh62P2h71Rh84valsp;1p;2p;4p;3p;5p;6g0045j15Tg004Zj1FTg0058j17Tg00:aj1PTg005[j10Tg00d6j2OTg00eZj1GTg00f9j2NTg00h3j4LTg00Q4j31Tg00hij1DTg00m1j3ITg006@j16Tg00j>j3?Tg01jUj2>Tg00FZj22Tg01kNj2<Tg00R_R0j2HTg01kmj2;Tg01m6j24Tg007Dj2BTg012=j1ATg01n?j5:Tg0023j6=Tg01oCj3MTg006^j2ETg013Fj1JTg01ogj4@Tf0R1#5#5p=3g00WlR2g00W2R3711p=9%01#0p=C%01#0#0#0p=K%01#0#0#0#0#0#0#0p=8g008VR4#5R5#3R6#5#3R7#FR8#7R9#P%05R5#FR:/O9f1R;g01b\#G#GR<'Np,3AMBp,3a0sp,4pathp,4envvCLR=519f2R>#Dg01c;R?;I;%06#6g00cZR65?:R@,>>RA,28%04R4#0RB#5#3#6RC512%55#6=?:6RD,>>REg020BRF519RG%05#6=?:6R5,>>RH=19=RI%34#6=?:6R6,>>R:,28g021<R4'<#9RJ'HRK'HP9f3RL#DRM1;?@'41281RN=12CX091B2C%AC,4M,28=12CePAPMP?P>P@P1D:E=PGPKP91;?D,4MA191FX09g022CRK%71RG%7;R@P0%7>?1;112L>12L;512R0[12>;12>1512%7L?1>;[RAf4#7?1L>\0AM>;1P1n2001000000120000000W2W1W3PA^2@^1G^3KP1P8%CB#K#8#8#8#8#8#8#3#0#C#3#6RB,E8PF128F,B2O4b4%AB,4M=19FePEPMP?P>PDP1D:E=PIPJP91;?5,4MA191=X09P;%J<,4M=19=ePHPMP?P>P5P1D:E=P91;?6,4M1<N4#9X091B23%57#3#3#3#3#6R7,E8,28/<4#9d%A7,4M,28/<4#9eP:PMP?P>P6P1D:E=C@C@C@W5W6W7W8o"). Qed.

  Lemma path_facts :
    rdn RSEGS mem0 (p1 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (p1 a0s path envv))%Z
    /\ (bv_unsigned (p1 a0s path envv) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length path) <= 131071)%Z.
  Proof.
    destruct (main_str sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen.
    exact (conj Sr (conj Slo (conj Shi Slen))).
  Qed.

  (* [comment removed for export] *)
  Lemma open_pipeline_gen : forall fd3 KA KB,
    (forall (R : bvmap 5 word) (M : word -> option byte),
       bv_unsigned (getr R 17) = 56%Z -> getr R 10 = AT_FDCWD ->
       Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z ->
       rdn RSEGS M (getr R 11) (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
       (bv_unsigned (getr R 11) + Z.of_nat (length path) < TASK_SIZE)%Z ->
       (forall e, In e openat_errnos ->
          realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0x43d64) 4) M (seg_rom RSEGS)) model0) KA) ->
       realizes RSEGS (mkCfg (mkst (regupd R 10 (alloc_fd (m_fds model0))) (v_addi (Z_to_bv 64 0x43d64) 4) M (seg_rom RSEGS))
                            (with_fds (fd_insert (m_fds model0) (alloc_fd (m_fds model0)) fd3) model0)) KB ->
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x43d64) M (seg_rom RSEGS)) model0) (t_alt2 KA KB)) ->
    open_err_branch KA -> at_malloc fd3 KB ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x17868) mem0 (seg_rom RSEGS)) model0) (t_alt2 KA KB).
  Proof.
    intros fd3 KA KB NODE HKA HKB.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & Slen). pose proof (u64_range (p1 a0s path envv)) as Hpr.
    rewrite model0_OF.
    apply (V2OpenFail.of_blockA sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Htid ME).
    intros vals R M HL P0 P2 P1 P5 HR HK Habove Hout. rewrite <- model0_OF.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    apply (NODE R M A17 A10 A12).
    - rewrite A11, <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - rewrite A11.
      assert (Hft : (bv_unsigned (p1 a0s path envv) + Z.of_nat (length path) + 1 <= TASK_SIZE)%Z)
        by (eapply path_fits_task; eassumption).
      lia.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x43d64 + 4)%Z with 0x43d68%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x43d64 + 4)%Z with 0x43d68%Z.
      rewrite model1_with_fds. rewrite m0_fds. unfold fds0. rewrite alloc_fd_init.
      pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      eapply (open_ok_blockB fd3 KB vals); try eassumption.
  Qed.

  (* [comment removed for export] *)
  Theorem open_file_pipeline : forall fdata KA KB,
    fs_lookup fs0 path = Some fdata -> path <> [] -> path <> dot_path -> (length path <= 4095)%nat ->
    open_err_branch KA -> at_malloc (FdFile path (Z_to_bv 64 0)) KB ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x17868) mem0 (seg_rom RSEGS)) model0) (t_alt2 KA KB).
  Proof.
    intros fdata KA KB Hfile Hpne Hpnd Hplen HKA HKB.
    apply (open_pipeline_gen (FdFile path (Z_to_bv 64 0)) KA KB); [| exact HKA | exact HKB].
    intros R M A17 A10 A12 Hstr Htask HA HB.
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x43d64) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_file_at RSEGS R _ M model0 ECALLW path fdata KA KB m0_pure HF is_ecall_ECALLW A17 A10 A12).
    - apply (read_cstr_of_rdn RSEGS M _ path Hplen path_nonul Htask Hstr).
    - exact Hpne.
    - apply (V2OpenFail.path_plain a0s path Hva). exact Hpnd.
    - rewrite m0_fs. exact Hfile.
    - rewrite m0_fds. apply fd_lookup_init_3.
    - exact HA.
    - exact HB.
  Qed.

  (* [comment removed for export] *)
  Theorem open_dir_pipeline : forall KA KB,
    path = dot_path ->
    open_err_branch KA -> at_malloc FdDir KB ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x17868) mem0 (seg_rom RSEGS)) model0) (t_alt2 KA KB).
  Proof.
    intros KA KB Hdot HKA HKB.
    apply (open_pipeline_gen FdDir KA KB); [| exact HKA | exact HKB].
    intros R M A17 A10 A12 Hstr Htask HA HB.
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x43d64) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_dir_at RSEGS R _ M model0 ECALLW KA KB m0_pure HF is_ecall_ECALLW A17 A10 A12).
    - replace Uapi.dot_path with path by (rewrite Hdot; reflexivity).
      apply (read_cstr_of_rdn RSEGS M _ path ltac:(rewrite Hdot; cbn; lia) path_nonul Htask Hstr).
    - rewrite m0_fds. apply fd_lookup_init_3.
    - exact HA.
    - exact HB.
  Qed.
End Open.
