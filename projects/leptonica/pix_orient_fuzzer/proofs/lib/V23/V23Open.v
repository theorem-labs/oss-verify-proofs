(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput; the vDSO; the recorded proofs decoded and re-encoded where p0 and p1, the argv and path pointers, lost the stack-pointer argument and took the Amb instance; the recorded proofs of open_ok_blockB, made over the old 8 MiB launch stack window, and of path_facts, made over cat_argv_ptr's old arguments, replaced by leptonica/kernel_fuzzer's plain proofs, addresses mapped; kernel_fuzzer's path_fits_task, the read_cstr range premise, added). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymCall.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib SpecConsts
  SymExec RefNodes RefNodesFS PureModel RefMemcpyLib Hoare MemSplit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Startup V23MainEntry V23OpenFail_defs V23OpenFail V23Open_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Open () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes6option01I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib6Common9CliDriver3Amb8mkModelCC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c59OSSVerify5KrLib3V237V23Open4fds0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open3vm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23OpenFail6model0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open6model0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open5fds1gC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00c59OSSVerify5KrLib3V237V23Open7model1gC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01c59OSSVerify5KrLib3V237V23Open7out_winC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3subc59OSSVerify5KrLib3V237V23Open9above_sp0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalK47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathK47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib3V237V23Open9at_mallocC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23MainEntry2p1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open3ENVC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open7m1_pureC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9PureModel9mp_haltedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCallAmem_denot_out_winC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive6rz_runC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgKTgt_pix_orient_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~____________________C59OSSVerify5KrLib3V23@V23OpenFail_defs4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23Open_defs6STOPS2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23@V23OpenFail_defs4scr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23Open_defs6o_srB0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23@V23OpenFail_defs3knAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib3V23@V23OpenFail_defs3srAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall3WINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5ldiffC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic3and01C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8AT_FDCWDC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBopen_ignored_flagsI47Corelib7Numbers7BinNums1N00C47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3V23<V23MainEntry8main_strC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC47Corelib4Init3Nat3addC59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC59OSSVerify5KrLib6Common8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State8alloc_fdC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsc59OSSVerify5KrLib3V237V23Open?open_err_branchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23OpenFail3ENVC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open;openat_regsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr03C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23<V23MainEntry6blobs0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_regsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX<env_app_knowC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_lC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC69OSSVerify5KrLib6Common9CliDriver9SymDriveX=vals_ev_app_rC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7add_0_rC69OSSVerify5KrLib6Common9CliDriver8SymDrive;regs_set_a0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive:v_addi_pc4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open>open_ok_blockBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open=alloc_fd_initC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open?model1_with_fdsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23OpenFail9of_blockAC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06C56Stdlib6ZArith4Znat5Nat2Z7inj_addC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosc59OSSVerify5KrLib3V237V23Open:path_factsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib3V237V23Open6m0_fdsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open9model0_OFC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupI47Corelib4Init5Peano2le00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC59OSSVerify5KrLib6Common7FileSim@read_cstr_of_rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23OpenFail:path_plainC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupc59OSSVerify5KrLib3V237V23Open@fd_lookup_init_3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23OpenAopen_pipeline_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:RefNodesFSArz_openat_file_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX6ECALLWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open7m0_pureC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver9SymDriveX?is_ecall_ECALLWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec8dot_pathC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open:path_nonulC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V237V23Open5m0_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FileSim3mrbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9read_cstrK4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result01C59OSSVerify5KrLib6Common:RefNodesFS@rz_openat_dir_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8dot_pathI4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result00".
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
ltac2:(KReplay.run1 (kr_t_V23Open ()) [] "h02e0h12e1h22e2p;1p;2p-1R0p10000p4p710p8P0p1000Gp4p710p8p1000gp4p70R0p1001Wp4p710R1p8P0p10023p4p710R0p8p1002Qp4p70R2P1p8P2P0p8p1003?p4p70R2P1p8P2P0p8g0045j10Tg004Zj16Tg0058j12Tg005[j11Tg006@j15Tg006^j24Tg007Dj23Tg007^R0g008VR2#0#0#0#0#0#0#6R1#2%12#5,41'3X20X10W0o"). Qed.
Lemma fd_lookup_init_3 : forall e0 e1 e2,
  fd_lookup [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] (Z_to_bv 64 3) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) [] "h02e0h12e1h22e2p;1p;2g009;j12Tg009]j11Tg007Dj20Tg007^R0%20%10'0X20X10W0o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "p;1p;2p;8g0045j10Tg004Zj13Tg0058j12Tg009]j11Tg00:?j27Tg00:aj16Tg00;Aj85Tg007Dj24Tg00<Cp,3AMBg00=9g00=np,6stdin0p,3fs0g008V#0#0#0R0#0#0#0#3#2R1#1p,3tid,71%30#2#6#1G5'4o"). Qed.
  Lemma model0_OF : model0 = V23OpenFail.model0 sp0 a0s path envv tid brk mbase fs0 stdin0 lim.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "p;;p;2g00>bl;1Tg007Dj20Tg00<Cp,3AMBp,3sp0p,3a0sp,4pathp,4envvp,3tidp,3brkp,5mbasep,3fs0p,6stdin0p,3limM;1'0o"). Qed.
  Lemma m0_fds : m_fds model0 = fds0.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "p;1p;2g0045j10Tg004Zj15Tg0058j12Tg00?]j21Tg00:aj14Tg007Dj23Tg008V#0#0#0#0#0#0#5#2g007^'1#4g00=9'3o"). Qed.
  Lemma m0_fs : m_fs model0 = fs0.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "p;2g007Dj20Tg002Qp,3fs0'0o"). Qed.
  Lemma m0_pure : md_pure model0.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "p;1p;2p;4g0045j10Tg004Zj19Tg0058j15Tg009;j14Tg009]j18Tg007Dj21Tg00?]j27Tg00:aj12Tg00@=j13Tg00@]j46Tg00A\g008V#0#0#0#0#0#0#9#5R0#4%80'11700R1#2%31'1%20%30'1C6o"). Qed.
  Lemma m1_fds : forall fd3, m_fds (model1g fd3) = fds1g fd3.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "h03fd3p;1p;2g0045j10Tg004Zj16Tg0058j12Tg00?]j21Tg00:aj15Tg00BSj14Tg007Dj23Tg007^R0g008V#0#0#0#0#0#0#6#2/10#5f0#4'3W0o"). Qed.
  Lemma m1_fs : forall fd3, m_fs (model1g fd3) = fs0.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "h03fd3p;2g007Dj20Tg007^g002Qp,3fs0'0W0o"). Qed.
  Lemma m1_vmmaps : forall fd3, m_vmmaps (model1g fd3) = vm0.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "h03fd3p;2g007Dj20Tg007^g00CIg00=n'0W0o"). Qed.
  Lemma m1_pure : forall fd3, md_pure (model1g fd3).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "h03fd3p;1p;2p;4g00D@j1:Tg0045j10Tg004Zj16Tg0058j14Tg009;j19Tg009]j18Tg007Dj21Tg00?]j25Tg00:aj12Tg00@=j13Tg00@]j47Tg007^f0#:g008V#0#0#0#0#0#0#6#4R0#9%80'11500R1#2%31'1%20%30'1C7W0o"). Qed.
  Lemma fds1_2 : forall fd3, fd_lookup (fds1g fd3) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "h03fd3p;1p;2g009;j17Tg0045j10Tg004Zj12Tg006@j11Tg006^j26Tg00E8j15Tg00:?j23Tg007Dj24Tg007^R0%70g008V#0R1#0#0#0#0#0#2%11'6#5,30'4W0o"). Qed.
  Lemma fds1_3 : forall fd3, fd_lookup (fds1g fd3) (Z_to_bv 64 3) = Some fd3.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "h03fd3p;1p;2g009;j12Tg00:?j21Tg007Dj20Tg007^R0%20f0,10'0W0o"). Qed.
  Lemma model1_with_fds : forall fd3,
    with_fds (fd_insert (m_fds model0) (alloc_fd (m_fds model0)) fd3) model0 = model1g fd3.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "h03fd3p;1p;2g00D@j11Tg007Dj20Tg007^g00<Cf0#1'0W0o"). Qed.

  (* [comment removed for export] *)
  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.
  (* [comment removed for export] *)
  Definition out_win (M : word -> option byte) : Prop :=
    forall a : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned a < bv_unsigned sp0)%Z -> M a = mem0 a.
  Lemma out_win_above : forall M, out_win M -> above_sp0 M.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "h02Hah14__p1h24__x1h34__x2h41Hh51Mh67__arithh74__ffh86__sat1h96__sat2h:8__varmaph;5__with<1ap;1p;2p;3p;4p;6p;7p;8g0045j12Tg004Zj17Tg0058j1;Tg009;j1VTg00F0j1LTg00Fhj23Tg00GRj21Tg006@j14Tg005[j19Tg00Gnj2?Tg00HVj25Tg00I2j2<Tg00IOj3UTg00@=j1TTg00:aj1STg00J3j2KTg00JQj1HTg00Joj4ETg00KMj1DTg00Kkj1CTg00LVj2:Tg00M9j48Tg009]j1BTg00Mdj6ATg00NHj7FTg00Nlj6GTg00OPj8@Tg00P4j2ITg007Dj2JTg00PVj2>Tg00QBj3MTg00Q\j3NTg00R;j4=Tg00Rmj2OTg00SHj2PTg00Sej1QTg00T_j7RTf0R0#2#2p=0f1R1g00UCR2g00UbR3P3g00VBR4P0g00VbFRp=6g008VR5#2R6#0R7#2#0R8#7R9#;R:%77#;#V[%L0p,3sp0,39R71390'1f2R;P1%46R<%96#9#2#4R='?g00WBR>/5<11>=1<<=R?,5>[[11><R@g00W`RAAU<=1UW011>?\A^0@p-0R@g00X<RAg00XZR?#T%S?PA1KA;P1%HACE%DA%CAR?P2P3P3P4PA1:A5R5g00YF1:A6R6C8,6?%B3P?P2P3P3P4P?P2P3P3P4P?P2P3P3P4f4R3EAPAP6g00YmP5C8,6?FFEGG@1I?4P0P;g00ZTR?g00[4R4'J1>0;=M?4dANA>1C=b7b:b;X2AW3W11101f3R>15;1'Og00[T[[^2A^3A^1@P0%28#0#0#0#0#0#0#0#0#4,P71393R3'1P3P7P>O4b6b8b9O2W0X<:%Q1eW4W5o"). Qed.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "p'0h01Hh12H0h21li001lh32H1h42Hlh52Hxh61ah71eh82H2h91xi011xh:2Hnh;2_Hh<3_H0h=3_H1h>3_H2h?1vp;1p;3p;2p;6g006@j1<Tg0045j16Tg004Zj1DTg0058j1KTg00:aR0j1BTg00@=j1HTg00\1j34Tg000Gj2>Tg00\Qj1=Tg00GRj27Tg00RmR1j25Tg00]1j1CTg00]mR2j33Tg006^j2JTg00^Nj3:Tg00^ej1;Tg00_>j1ITg00QBj30Tg00`Bj2GTg00a6j2FTg001Wj6?Tg00aMj2ETg00alj68Tg0023j69Tg007Dj2@Tg005[j1ATf0R3#6#6p=1%A3#Ap=2p,3Hvag008VR4#<%64#1R5#DR6#KR7#BR8p,3a0sR9p,4pathR:%H8R;548R<548R='>#=R>'7%65#1#1#1R5#<,7>'5R>%C=%65#1#1#1#1#1#<'7R51>73#=%24#2#2#2#2#2#2#2#<'7X68=38=R4g00WB,J6R6=:73#;X68R?=38=R@g000gRAg00ZTRB%I3g00bIRC30g00bi,G3=0BC'5X6A1F8=33RA'5RC'5RB'5RD'5P1P>PDA:76:#;REP3P1P5PBPEP3P1P4PCPEP3P1P@PAPEP3P2P8P?%B8R1f1RF;0=PE[PFA01;=RGP1P;P0P8p-0P3g00W`g00[TRHn10110000020020000000X71RIg00cjRJP=P3E?PH1EE3RKb1X0GP3O1W0A:76F#;RGA38?FRLf3RMf2RN548RO=01=f4RP=48MRQ=01=P1P1P0P8P1P3f5RRP3n10110000020020100100X71RSA48RPRTP=P3E8A01P<P1P8P0P8P8P3f7R0PFn10110000020020100100X71RUf6RV=48RRRP=PFE8A08V9A0809P3f8RW=089P8P9f9RX=01<RYf;938?RZPE]4^5G[X28A01W<P3PYP1P<A:769#;R6PE^4L]5X21A38?<P2P8P?A01F<PE[P3A01;<R2P1P;PIPJP<P3E?PHPKb1X02P3O1W0A01O<A01Q<P1P1PSPTP<P3E8A01P;P1P8PUPRP<PFE8A08V:A080:P3A08W:P8P:A01X;R:PE^1Z^0G[X28A01W;P3P:P1P;PE^1L^0EX21A38?;PFW8X3Ef:R?P3E9b8W1PXP3E9b1W0P3O1b0P3O1b0W3P3PNPFO3W3X1LX0GX21X98PMPNPFP3O4n200210000000020041101100000000A013<PE[X21P<O1P31@1<O1b0W4X56P?P3E9b3W1PXP3E9b1W0P3O1b1P3O1b1W0P3PNPFO3W0W4W5X21X98PMPNPFP3O4n200210000000020141101100000000A013=PE[X21P=O1P31@1=O1b0X>AX:@PFP3O2n2001000000121000000X0CX=4PFP3O2n2001000000121000000X0BX<5PFP3O2n2011000000121000000X0DX;>PFP3O2n2011000000121000000b?o"). Qed.

  (* [comment removed for export] *)
  Definition open_err_branch (KA : TSet) : Prop :=
    forall e vals R M,
      In e openat_errnos ->
      length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
      vals_ev vals 1 = p0 a0s path envv -> vals_ev vals 2 = p1 a0s path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
      above_sp0 M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x11eff4) M (seg_rom RSEGS)) model0) KA.

  (* [comment removed for export] *)
  Definition at_malloc (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 38%nat -> vals_ev vals 0 = sp0 ->
      vals_ev vals 1 = p0 a0s path envv -> vals_ev vals 2 = p1 a0s path envv -> vals_ev vals 5 = tid ->
      regs_ok (ENV vals) o_srB R -> know_ok RSEGS (ENV vals) M o_knB ->
      out_win M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x10e958) M (seg_rom RSEGS)) (model1g fd3)) KB.

  (* [comment removed for export] *)
  Lemma open_ok_blockB : forall fd3 KB vals R M,
    at_malloc fd3 KB ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 ->
    vals_ev vals 1 = p0 a0s path envv -> vals_ev vals 2 = p1 a0s path envv -> vals_ev vals 5 = tid ->
    regs_ok (ENV vals) (sr_upd srA (ridx 10) (ELit 3)) R -> know_ok RSEGS (ENV vals) M knA ->
    out_win M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x11eff4) M (seg_rom RSEGS)) (model1g fd3)) KB.
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
ltac2:(KReplay.run1 (kr_t_V23Open ()) ["Open"] "p%0p'0p%1p'1p%2p'2p%3p'3p%4p'4p%5p'5p%6p'6p%7p'7p%8p'8p%9p'9p%:p':p%;p';p%<p'<p%=p'=p%>p'>p%?p'?p%@p'@p%Ap'Ap%Bp'Bp%Cp'Cp%Dp'Dp%Ep'Ep%Fp'Fp%Gp'Gp%Hp'Hp%Ip'Ip%Jp'Jp%Kp'Kp%Lp'Lp%Mp'Mp%Np'Np%Op'Op%Pp'Pp%Qp'Qp%Rp'Rp%Sp'Sp%Tp'Tp%Up'Up%Vp'Vp%Wp'Wp%Xp'Xp%Yp'Yp%Zp'Zp%[p'[p%\p'\p%]p']p%^p'^p%_p'_p%`p'`p%ap'ap%bp'bp%cp'cp%dp'dp%ep'ep%fp'fp%gp'gp%hp'hp%ip'ip%jp'jp%kp'kp%lp'lp%mp'mp%np'np%op'op%pp'pp%qp'qp%rp'rp%sp'sp%tp'tp%up'up%vp'vp%wp'wp%xp'xp%yp'yp%zp'zp%{p'{p%|p'|p%}p'}p%~p'~p/I47Corelib4Init9Datatypes4list00p/I45stdpp9bitvector;definitions2bv00p/K47Corelib7Numbers7BinNums1N02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive03O1O1O1S03O1O1O1S02O1S01O1S00O1p/C4ELinuxProcessSemantics5Riscv7Prelude5bvmapp/K47Corelib7Numbers7BinNums1N02p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive03O1O1S05O1S04Q00O2p/I47Corelib4Init5Logic2eq00Q00p/C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evf1p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat01O1O1S06O2p/C59OSSVerify5KrLib3V23<V23MainEntry2p1p,3AMBp,3a0sp,4pathp,4envvO4S07O3p/C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okp/c59OSSVerify5KrLib3V237V23Open3ENVf2O1p/C59OSSVerify5KrLib3V23@V23OpenFail_defs3srAf1O3p/K47Corelib4Init5Logic3and01p/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C45stdpp9bitvector;definitions;bv_unsignedQ01p/C59OSSVerify5KrLib6Common8PropExec4getrf2p/K45stdpp9bitvector;definitions2bv01Q04p/K47Corelib7Numbers7BinNums1Z02p/K47Corelib7Numbers7BinNums8positive01Q03O1O1p/K47Corelib4Init5Logic4True01O3S08O2O2p/K47Corelib7Numbers7BinNums1Z02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive03O1O1S0:O1O1O1O1S09O3p/I47Corelib4Init5Logic3and00p/I47Corelib4Init5Logic2eq00Q00p/C59OSSVerify5KrLib6Common8PropExec4getrf2p/K45stdpp9bitvector;definitions2bv01Q04p/K47Corelib7Numbers7BinNums1Z02p/K47Corelib7Numbers7BinNums8positive02Q05O1O1p/K47Corelib4Init5Logic4True01O3S0;O2p/C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8AT_FDCWDO3p/I47Corelib4Init5Logic3and00p/I47Corelib4Init5Logic2eq00Q00p/C59OSSVerify5KrLib6Common8PropExec4getrf2p/K45stdpp9bitvector;definitions2bv01Q04p/K47Corelib7Numbers7BinNums1Z02p/K47Corelib7Numbers7BinNums8positive01Q05O1O1p/K47Corelib4Init5Logic4True01O3S0<O2Q07O3p/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C56Stdlib6ZArith6BinInt1Z5ldiffp/C45stdpp9bitvector;definitions;bv_unsignedQ01p/C59OSSVerify5KrLib6Common8PropExec4getrf2p/K45stdpp9bitvector;definitions2bv01Q04p/K47Corelib7Numbers7BinNums1Z02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive03O1O1O1O1p/K47Corelib4Init5Logic4True01O3S0=O2O2p/C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBopen_ignored_flagsO2p/K47Corelib7Numbers7BinNums1Z01O3O2O2p/C47Corelib4Init5Logic8eq_ind_rQ00p/C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotp/c59OSSVerify5KrLib3V237V23Open3ENVf3O1p/C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getp/C59OSSVerify5KrLib3V23@V23OpenFail_defs3srAQ08O2O2Q00p/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C45stdpp9bitvector;definitions;bv_unsignedQ01f0O2Q09O3i001bpB0100p/K47Corelib4Init5Logic2eq01p/I47Corelib7Numbers7BinNums1Z00Q09O2p/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C45stdpp9bitvector;definitions;bv_unsignedQ01p/C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotp/c59OSSVerify5KrLib3V237V23Open3ENVf3O1p/K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01Q09O1O2O2Q09O3ep/C59OSSVerify5KrLib6Common8PropExec4getrf2Q08O2p/C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valp/c59OSSVerify5KrLib3V237V23Open3ENVf3O1p/C59OSSVerify5KrLib3V23@V23OpenFail_defs3srAf2Q08f0O5O6p/K47Corelib4Init5Logic3and01p/I47Corelib4Init5Logic2eq00Q00p/C59OSSVerify5KrLib6Common8PropExec4getrf2Q0;O2p/C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8AT_FDCWDO3p/I47Corelib4Init5Logic3and00p/I47Corelib4Init5Logic2eq00Q00p/C59OSSVerify5KrLib6Common8PropExec4getrf2Q0<O2Q07O3p/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C56Stdlib6ZArith6BinInt1Z5ldiffp/C45stdpp9bitvector;definitions;bv_unsignedQ01p/C59OSSVerify5KrLib6Common8PropExec4getrf2Q0=O2O2p/C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBopen_ignored_flagsO2p/K47Corelib7Numbers7BinNums1Z01O3O2p/C47Corelib4Init5Logic8eq_ind_rQ00p/C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotp/c59OSSVerify5KrLib3V237V23Open3ENVf3O1p/C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getp/C59OSSVerify5KrLib3V23@V23OpenFail_defs3srAQ0;O2O2Q00p/I47Corelib4Init5Logic2eq00Q00f0p/C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8AT_FDCWDO3i001bpB0100p/I47Corelib7Numbers7BinNums1N00p/I45stdpp9bitvector;definitions2bv00f0O1p/I45stdpp9bitvector;definitions2bv00f1O1p/I47Corelib4Init5Logic3and00p/I47Corelib4Init5Logic2eq00p/I45stdpp9bitvector;definitions2bv00f2O1f1f0O3p/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C45stdpp9bitvector;definitions;bv_unsignedf3f2O2p/C45stdpp9bitvector;definitions;bv_unsignedf3f1O2O3pB1000p/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C45stdpp9bitvector;definitions;bv_unsignedf2f1O2p/C45stdpp9bitvector;definitions;bv_unsignedf2f0O2O3p/I47Corelib4Init5Logic2eq00p/I45stdpp9bitvector;definitions2bv00f3O1f2f1O3pB1000p/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C45stdpp9bitvector;definitions;bv_unsignedf3f2O2p/C45stdpp9bitvector;definitions;bv_unsignedf3f1O2O3p/I47Corelib4Init5Logic2eq00p/I45stdpp9bitvector;definitions2bv00f4O1f3f2O3pB1000p/C45stdpp9bitvector;definitions5bv_eqf2f1f0O3f0n2001000000120000000i002b2pB0100i002b1pB0100i001npB0100p/I47Corelib7Numbers7BinNums1N00p/I45stdpp9bitvector;definitions2bv00f0O1p/I45stdpp9bitvector;definitions2bv00f1O1p/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C45stdpp9bitvector;definitions;bv_unsignedf2f1O2p/C45stdpp9bitvector;definitions;bv_unsignedf2f0O2O3p/I47Corelib4Init5Logic2eq00p/I45stdpp9bitvector;definitions2bv00f3O1f2f1O3pB1000i002b2pB1100i002b1pB1100i001npB1100f0Q01p/C45stdpp9bitvector;definitions7Z_to_bvQ01p/K47Corelib7Numbers7BinNums1Z02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01Q0:O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1S0>O2p/C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8AT_FDCWDp/K47Corelib4Init5Logic2eq01p/I47Corelib7Numbers7BinNums1Z00p/C45stdpp9bitvector;definitions;bv_unsignedQ01p/C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8AT_FDCWDO2O2O4i001HpB2100p/I47Corelib4Init5Logic2eq00Q00p/C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotp/c59OSSVerify5KrLib3V237V23Open3ENVf3O1p/K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01Q0>O1O2p/C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8AT_FDCWDO3ep/C59OSSVerify5KrLib6Common8PropExec4getrf2Q0;O2p/C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valp/c59OSSVerify5KrLib3V237V23Open3ENVf3O1p/C59OSSVerify5KrLib3V23@V23OpenFail_defs3srAf2Q0;f0O5O6p/K47Corelib4Init5Logic3and01p/I47Corelib4Init5Logic2eq00Q00p/C59OSSVerify5KrLib6Common8PropExec4getrf2Q0<O2Q07O3p/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C56Stdlib6ZArith6BinInt1Z5ldiffp/C45stdpp9bitvector;definitions;bv_unsignedQ01p/C59OSSVerify5KrLib6Common8PropExec4getrf2Q0=O2O2p/C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBopen_ignored_flagsO2p/K47Corelib7Numbers7BinNums1Z01O3p/C47Corelib4Init5Logic8eq_ind_rQ00p/C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotp/c59OSSVerify5KrLib3V237V23Open3ENVf3O1p/C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getp/C59OSSVerify5KrLib3V23@V23OpenFail_defs3srAQ0<O2O2Q00p/I47Corelib4Init5Logic2eq00Q00f0Q07O3i001bpB0100f1p/I47Corelib4Init5Logic2eq00Q00p/C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotp/c59OSSVerify5KrLib3V237V23Open3ENVf3O1p/K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02Q06O1O2Q07O3ep/C59OSSVerify5KrLib6Common8PropExec4getrf2Q0<O2p/C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valp/c59OSSVerify5KrLib3V237V23Open3ENVf3O1p/C59OSSVerify5KrLib3V23@V23OpenFail_defs3srAf2Q0<f0O5O6p/C47Corelib4Init5Logic8eq_ind_rQ00p/C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotp/c59OSSVerify5KrLib3V237V23Open3ENVf3O1p/C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getp/C59OSSVerify5KrLib3V23@V23OpenFail_defs3srAQ0=O2O2Q00p/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C56Stdlib6ZArith6BinInt1Z5ldiffp/C45stdpp9bitvector;definitions;bv_unsignedQ01f0O2p/C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBopen_ignored_flagsO2p/K47Corelib7Numbers7BinNums1Z01O3i001bpB0100p/K47Corelib4Init5Logic2eq01p/I47Corelib7Numbers7BinNums1Z00p/K47Corelib7Numbers7BinNums1Z01O2p/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C56Stdlib6ZArith6BinInt1Z5ldiffp/C45stdpp9bitvector;definitions;bv_unsignedQ01p/C45stdpp9bitvector;definitions7Z_to_bvQ01p/K47Corelib7Numbers7BinNums1Z02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02Q02O1O1O1O1O1O1O1O1O1O1S0?O2O2p/C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBopen_ignored_flagsO2p/K47Corelib7Numbers7BinNums1Z01O3dp/I47Corelib4Init5Logic2eq00p/I47Corelib7Numbers7BinNums1Z00p/C56Stdlib6ZArith6BinInt1Z5ldiffp/C45stdpp9bitvector;definitions;bv_unsignedQ01p/C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotp/c59OSSVerify5KrLib3V237V23Open3ENVf3O1p/K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01Q0?O1O2O2p/C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBopen_ignored_flagsO2p/K47Corelib7Numbers7BinNums1Z01O3ep/C59OSSVerify5KrLib6Common8PropExec4getrf2Q0=O2p/C69OSSVerify5KrLib6Common9CliDriver6SymRun7reg_valp/c59OSSVerify5KrLib3V237V23Open3ENVf3O1p/C59OSSVerify5KrLib3V23@V23OpenFail_defs3srAf2Q0=f0O5O6O4O4O4i002HRpB0100i002P2pB0100i001RpB0100i004valspB0100o"). Qed.

  Lemma path_facts :
    rdn RSEGS mem0 (p1 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (p1 a0s path envv))%Z
    /\ (bv_unsigned (p1 a0s path envv) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length path) <= 131071)%Z.
  Proof.
    destruct (main_str sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen. unfold p1. repeat split; assumption.
  Qed.

  (* the path string ends below TASK_SIZE: the read_cstr lemmas' range premise *)
  Lemma path_fits_task : (bv_unsigned (p1 a0s path envv) + Z.of_nat (length path) + 1 <= TASK_SIZE)%Z.
  Proof. exact (me_argv_fits sp0 [a0s; path] envv tid regs0 mem0 ME Hva Hve Hvsp 1%nat ltac:(cbn; lia)). Qed.

  (* [comment removed for export] *)
  Lemma open_pipeline_gen : forall fd3 KA KB,
    (forall (R : bvmap 5 word) (M : word -> option byte),
       bv_unsigned (getr R 17) = 56%Z -> getr R 10 = AT_FDCWD ->
       Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z ->
       rdn RSEGS M (getr R 11) (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
       (bv_unsigned (getr R 11) + Z.of_nat (length path) < TASK_SIZE)%Z ->
       (forall e, In e openat_errnos ->
          realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0x11eff0) 4) M (seg_rom RSEGS)) model0) KA) ->
       realizes RSEGS (mkCfg (mkst (regupd R 10 (alloc_fd (m_fds model0))) (v_addi (Z_to_bv 64 0x11eff0) 4) M (seg_rom RSEGS))
                            (with_fds (fd_insert (m_fds model0) (alloc_fd (m_fds model0)) fd3) model0)) KB ->
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x11eff0) M (seg_rom RSEGS)) model0) (t_alt2 KA KB)) ->
    open_err_branch KA -> at_malloc fd3 KB ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x63140) mem0 (seg_rom RSEGS)) model0) (t_alt2 KA KB).
  Proof.
    intros fd3 KA KB NODE HKA HKB.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & Slen). pose proof (u64_range (p1 a0s path envv)) as Hpr.
    rewrite model0_OF.
    apply (V23OpenFail.of_blockA sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Htid ME).
    intros vals R M HL P0 P2 P1 P5 HR HK Habove Hout. rewrite <- model0_OF.
    destruct (openat_regs vals R P2 HR) as (A17 & A10 & A11 & A12).
    apply (NODE R M A17 A10 A12).
    - rewrite A11, <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - rewrite A11. pose proof path_fits_task. lia.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x11eff0 + 4)%Z with 0x11eff4%Z.
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
      rewrite v_addi_pc4 by lia. change (0x11eff0 + 4)%Z with 0x11eff4%Z.
      rewrite model1_with_fds. rewrite m0_fds. unfold fds0. rewrite alloc_fd_init.
      pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      eapply (open_ok_blockB fd3 KB vals); try eassumption.
  Qed.

  (* [comment removed for export] *)
  Theorem open_file_pipeline : forall fdata KA KB,
    fs_lookup fs0 path = Some fdata -> path <> [] -> path <> dot_path -> (length path <= 4095)%nat ->
    open_err_branch KA -> at_malloc (FdFile path (Z_to_bv 64 0)) KB ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x63140) mem0 (seg_rom RSEGS)) model0) (t_alt2 KA KB).
  Proof.
    intros fdata KA KB Hfile Hpne Hpnd Hplen HKA HKB.
    apply (open_pipeline_gen (FdFile path (Z_to_bv 64 0)) KA KB); [| exact HKA | exact HKB].
    intros R M A17 A10 A12 Hstr Htask HA HB.
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x11eff0) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_file_at RSEGS R _ M model0 ECALLW path fdata KA KB m0_pure HF is_ecall_ECALLW A17 A10 A12).
    - apply (read_cstr_of_rdn RSEGS M _ path Hplen path_nonul Htask Hstr).
    - exact Hpne.
    - apply (V23OpenFail.path_plain a0s path Hva). exact Hpnd.
    - rewrite m0_fs. exact Hfile.
    - rewrite m0_fds. apply fd_lookup_init_3.
    - exact HA.
    - exact HB.
  Qed.

  (* [comment removed for export] *)
  Theorem open_dir_pipeline : forall KA KB,
    path = dot_path ->
    open_err_branch KA -> at_malloc FdDir KB ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x63140) mem0 (seg_rom RSEGS)) model0) (t_alt2 KA KB).
  Proof.
    intros KA KB Hdot HKA HKB.
    apply (open_pipeline_gen FdDir KA KB); [| exact HKA | exact HKB].
    intros R M A17 A10 A12 Hstr Htask HA HB.
    assert (HF : fetch_word RSEGS (Z_to_bv 64 0x11eff0) = Some ECALLW) by (vm_compute; reflexivity).
    eapply (rz_openat_dir_at RSEGS R _ M model0 ECALLW KA KB m0_pure HF is_ecall_ECALLW A17 A10 A12).
    - replace Uapi.dot_path with path by (rewrite Hdot; reflexivity).
      apply (read_cstr_of_rdn RSEGS M _ path ltac:(rewrite Hdot; cbn; lia) path_nonul Htask Hstr).
    - rewrite m0_fds. apply fd_lookup_init_3.
    - exact HA.
    - exact HB.
  Qed.
End Open.
