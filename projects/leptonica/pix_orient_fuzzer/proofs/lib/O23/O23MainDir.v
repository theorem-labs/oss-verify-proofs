(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs decoded and re-encoded where p0 and p1, the argv and path pointers, lost the stack-pointer argument and took the Amb instance). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibTail SymCall.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib LibWritev PureModel VmLedger AllocIface MemSplit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MallocLayout O23ExitBase O23Startup O23StartupDefs O23StartupFacts O23MainEntry O23LibStdioCall O23OpenFail_defs O23OpenFail_tail2 O23Open_defs O23Open O23Oom_defs O23MemPreds O23ReadErr O23Malloc65536 O23DirRead_defs O23DirRead O23OpenFailBranch.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23MainDir () := "C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib6Common9CliDriver4Spec?msg_cannot_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec>msg_read_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23AO23OpenFailBranchKopen_err_branch_cannot_openC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open7out_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23DirRead>dir_read_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23>O23Malloc65536@malloc65536_nodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open9at_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23OpenAopen_dir_pipelineC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Spec<t_opened_dirC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib6Common9CliDriver4Spec8dot_pathC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib3O23<O23Open_defs5o_srBC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23Open_defs5o_knBC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

Section MainDir.
  Context {AMB : Amb} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
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

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let ENV := O23Open.ENV a0s path.
  Let model1g := O23Open.model1g sp0 tid brk mbase fs0 stdin0 lim.

  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  (* [comment removed for export] *)
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0xfa4b4.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x123d20.
  Hypothesis AL_glob : forall a, al_globals a -> (0x144020 <= bv_unsigned a < 0x1443d0)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x145000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x123c7c <= bv_unsigned a < 0x123c80)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x145000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x145000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x145000)%Z.
  Hypothesis AL_ret : forall z, In z [0x62b70; 0x62b9c; 0x62c18; 0x62d18; 0x62e48]%Z -> al_ret_ok (Z_to_bv 64 z).
  Hypothesis AL_env : forall M, O23Malloc65536.env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.

  Let model0 := O23Open.model0 sp0 a0s path envv tid brk mbase fs0 stdin0 lim.

  (* [comment removed for export] *)
  Theorem ref_dir_path :
    path = dot_path ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x62b1c) mem0 (seg_rom RSEGS)) model0)
             (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)).
Proof.
ltac2:(KReplay.run1 (kr_t_O23MainDir ()) ["MainDir"] "p%0p'0p%1p'1p%2p'2p%3p'3p%4p'4p%5p'5p%6p'6p%7p'7p%8p'8p%9p'9p%:p':p%;p';p%<p'<p%=p'=p%>p'>p%?p'?p%@p'@p%Ap'Ap%Bp'Bp%Cp'Cp%Dp'Dp%Ep'Ep%Fp'Fp%Gp'Gp%Hp'Hp%Ip'Ip%Jp'Jp%Kp'Kp%Lp'Lp%Mp'Mp%Np'Np%Op'Op%Pp'Pp%Qp'Qp%Rp'Rp%Sp'Sp%Tp'Tp%Up'Up%Vp'Vp%Wp'Wp%Xp'Xp%Yp'Yp%Zp'Zp%[p'[p%\p'\p%]p']p%^p'^p%_p'_p%`p'`p%ap'ap%bp'bp%cp'cp%dp'dp%ep'ep%fp'fp%gp'gp%hp'hp%ip'ip%jp'jp%kp'kp%lp'lp%mp'mp%np'np%op'op%pp'pp%qp'qp%rp'rp%sp'sp%tp'tp%up'up%vp'vp%wp'wp%xp'xp%yp'yp%zp'zp%{p'{p%|p'|p%}p'}p%~p'~p-1p0C46Stdlib5Lists4List2hdp4p710p8p/I47Corelib4Init5Logic2eq00p/I47Corelib4Init9Datatypes4list00p/I45stdpp9bitvector;definitions2bv00p/K47Corelib7Numbers7BinNums1N02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive03O1O1O1S01O1O1S00O1p,4pathp/C69OSSVerify5KrLib6Common9CliDriver4Spec8dot_pathO3p/C59OSSVerify5KrLib3O237O23OpenAopen_dir_pipelinep,3AMBp,3sp0p,3a0sp,4pathp,4envvp,3tidp,5regs0p,4mem0p,3brkp,5mbasep,3fs0p,6stdin0p,3limp,3Hvap,3Hvep,4Hvspp,4Htidp,2MEp/C69OSSVerify5KrLib6Common9CliDriver4Spec5t_diep/C69OSSVerify5KrLib6Common9CliDriver4Spec?msg_cannot_openp,4pathO1p,3fs0O2S02p/C69OSSVerify5KrLib6Common9CliDriver4Spec5t_diep/C69OSSVerify5KrLib6Common9CliDriver4Spec>msg_read_errorp,4pathO1p,3fs0O2S03f0p/C59OSSVerify5KrLib3O23AO23OpenFailBranchKopen_err_branch_cannot_openp,3AMBp,3sp0p,3a0sp,4pathp,4envvp,3tidp,5regs0p,4mem0p,3brkp,5mbasep,3fs0p,6stdin0p,3limp,3Hvap,3Hvep,4Hvspp,2MEp,5HfitsOBp/I47Corelib4Init9Datatypes4list00p/I45stdpp9bitvector;definitions2bv00p/K47Corelib7Numbers7BinNums1N02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02Q01O1O1O1O1S05O1S04O1p/C4ELinuxProcessSemantics5Riscv7Prelude5bvmapp/K47Corelib7Numbers7BinNums1N02p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive03O1O1O1Q04O2Q04p/I47Corelib4Init9Datatypes6option00Q00O1pB1000p/I47Corelib4Init5Logic2eq00p/I47Corelib4Init9Datatypes3nat00p/C47Corelib4Init9Datatypes6lengthQ04f2O2p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat01O1O1S07O1O1O1S06O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O3p/I47Corelib4Init5Logic2eq00Q04p/C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evf3p/K47Corelib4Init9Datatypes3nat01O2p,3sp0O3p/I47Corelib4Init5Logic2eq00Q04p/C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evf4p/K47Corelib4Init9Datatypes3nat02p/K47Corelib4Init9Datatypes3nat01O1O2p/C59OSSVerify5KrLib3O23<O23MainEntry2p0p,3AMBp,3a0sp,4pathp,4envvO4O3p/I47Corelib4Init5Logic2eq00Q04p/C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evf5Q07O2p/C59OSSVerify5KrLib3O23<O23MainEntry2p1p,3AMBp,3a0sp,4pathp,4envvO4O3p/I47Corelib4Init5Logic2eq00Q04p/C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evf6Q06O2p,3tidO3p/C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okp/C59OSSVerify5KrLib3O237O23Open3ENVp,3AMBp,3a0sp,4pathf7O4p/C59OSSVerify5KrLib3O23<O23Open_defs5o_srBf6O3p/C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okp/C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsp/C59OSSVerify5KrLib3O237O23Open3ENVp,3AMBp,3a0sp,4pathf8O4f6p/C59OSSVerify5KrLib3O23<O23Open_defs5o_knBO4p/C59OSSVerify5KrLib3O237O23Open7out_winp,3sp0p,4mem0f7O3p/C59OSSVerify5KrLib3O23>O23Malloc65536@malloc65536_nodep,3AMBp,2ALp,2CLp,3ASRp,3sp0p,3a0sp,4pathp,4envvp,3tidp,5regs0p,4mem0p,3brkp,5mbasep,3fs0p,6stdin0p,3limp,4Hvspp,4Htidp,2MEp,4Hbrkp,7AL_segsp,6AL_romp,9AL_mallocp,5AL_tpp,7AL_globp,8AL_grantp,8AL_errnop,5AL_rop,5AL_rwp,5AL_hip,6AL_retp,6AL_envp/K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06Q03p/C59OSSVerify5KrLib3O23:O23DirRead>dir_read_errorp,3AMBp,2ALp,2CLp,3ASRp,3sp0p,3a0sp,4pathp,4envvp,3tidp,5regs0p,4mem0p,3brkp,5mbasep,3fs0p,6stdin0p,3limp,3Hvap,3Hvep,4Hvspp,4Htidp,2MEf;OFf:f9f8f7f6f5f4f3f2f1f0O^i003HOWpB0100i002HKpB0100i002HRpB0100i002P5pB0100i002P2pB0100i002P1pB0100i002P0pB0100i002HLpB0100i001MpB0100i001RpB0100i004valspB0100p/C59OSSVerify5KrLib3O237O23Open9at_mallocp,3AMBp,3sp0p,3a0sp,4pathp,4envvp,3tidp,4mem0p,3brkp,5mbasep,3fs0p,6stdin0p,3limp/K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06Q03O>eOGp/I59OSSVerify5KrLib6Common8ShapeAlg8realizes00p/C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsp/K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01p/C59OSSVerify5KrLib6Common8PropExec4mkstp/C59OSSVerify5KrLib6Common8PropExec3fx0p,5regs0p/C45stdpp9bitvector;definitions7Z_to_bvQ05p/K47Corelib7Numbers7BinNums1Z02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive02p/K47Corelib7Numbers7BinNums8positive01p/K47Corelib7Numbers7BinNums8positive03O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O2p,4mem0p/C59OSSVerify5KrLib6Common8PropExec7seg_romp/C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsO1O5p,6model0O2p/C59OSSVerify5KrLib6Common8ShapeAlg6t_alt2Q02p/C69OSSVerify5KrLib6Common9CliDriver4Spec<t_opened_dirp,4pathp,3fs0O2O2O3ei004HdotpB0100o"). Qed.
End MainDir.
