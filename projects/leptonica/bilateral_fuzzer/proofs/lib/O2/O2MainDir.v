(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibTail SymCall.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib LibWritev PureModel VmLedger AllocIface MemSplit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MallocLayout O2ExitBase O2Startup O2StartupDefs O2StartupFacts O2MainEntry O2LibStdioCall O2OpenFail_defs O2OpenFail_tail2 O2Open_defs O2Open O2Oom_defs O2MemPreds O2ReadErr O2Malloc65536 O2DirRead_defs O2DirRead O2OpenFailBranch.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2MainDir () := "C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib6Common9CliDriver4Spec?msg_cannot_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec>msg_read_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2@O2OpenFailBranchKopen_err_branch_cannot_openC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open3ENVC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open7out_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O29O2DirRead>dir_read_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2Malloc65536@malloc65536_nodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open9at_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2OpenAopen_dir_pipelineC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Spec<t_opened_dirC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib6Common9CliDriver4Spec8dot_pathC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib2O2;O2Open_defs5o_srBC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2Open_defs5o_knBC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~".
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
  Let ENV := O2Open.ENV a0s path.
  Let model1g := O2Open.model1g sp0 tid brk mbase fs0 stdin0 lim.

  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  (* [comment removed for export] *)
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x2f94c.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x49840.
  Hypothesis AL_glob : forall a, al_globals a -> (0x69b38 <= bv_unsigned a < 0x69ee8)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x6b000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x4979c <= bv_unsigned a < 0x497a0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x6b000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x6b000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x6b000)%Z.
  Hypothesis AL_ret : forall z, In z [0x1766c; 0x17698; 0x17714; 0x17814; 0x17944]%Z -> al_ret_ok (Z_to_bv 64 z).
  Hypothesis AL_env : forall M, O2Malloc65536.env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.

  Let model0 := O2Open.model0 sp0 a0s path envv tid brk mbase fs0 stdin0 lim.

  (* [comment removed for export] *)
  Theorem ref_dir_path :
    path = dot_path ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x17618) mem0 (seg_rom RSEGS)) model0)
             (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)).
Proof.
ltac2:(KReplay.run1 (kr_t_O2MainDir ()) ["MainDir"] "h02HKh12HLh23HOWh32HRh44Hdoth51Mh62P0h72P1h82P2h92P5h:1Rh;4valsp;1p;3p;2p;Bp;4p;Fp;^p;>p;Gp;5p-1p10000p4p710p8g000Gj13Tg000lj17Tg001Jj1:Tg001mj1;Tg002Mj34Tg002gj1MTg0041j28Tg0051j1ATg006:lB@Tg007Nj11Tg0083j2=Tg008_j1<Tg009Aj2STg009aj10Tg00:@j26Tg00;Dj4QTg00<:j4LTg00=0j49Tg00=bj3KTg00?2j4CTg00@Bj3BTg00A8lFDTg00B8l^ETg00C>l>FTg00D6lGGTg00E6j1HTg00ETj2ITg00F:j1JTg00G6j5?Tg00Goj2>Tg00Hdj2NTg00Ikj2OTg00Jfj3PTf0R0#3#3p=5%00#0p=R%00#0#0#0p=2g00KeR1#3R2#5R3#7#:R4#;p,4pathR5g00LJ34p,3AMBR6p,3sp0R7p,3a0sR8P5p,4envvR9p,3tidR:p,5regs0R;p,4mem0R<p,3brkR=p,5mbaseR>p,3fs0R?p,6stdin0R@p,3limRAp,3HvaRBp,3HveRCp,4HvspRDp,4HtidREp,2MERF%M5/8?RG%A5/8?RHP0P6P7P8P5P9P:P;P<P=P>P?P@PAPBPCPDPFp,5HfitsMB@%33#5#7R3#:RI#;%12#7/=I%<4\Ig00MMf2R4,SIg00MlR2#0RJ#0RK#0#RRL#0#2#2#2#2#2#2#2#234f3RM/62=4I7f4R2/6JP7P8P5P9CQ54If5RJ/6KP7P8P5P9CL54If6RK/6L=4I:P6P8P5f7RIC9g00NK;KKg00ODRLP6P8P5f8RNC9PKg00PjCCAB7<IP6p,2ALROp,2CLRPp,3ASRRQP7P8P5P9P:P;P<P=P>P?P@PAPDPEPFp,4Hbrkp,7AL_segsp,6AL_romp,9AL_mallocp,5AL_tpp,7AL_globp,8AL_grantp,8AL_errnop,5AL_rop,5AL_rwp,5AL_hip,6AL_retp,6AL_envg00QcRRPHP6POPPPQP7P8P5P9P:P;P<P=P>P?P@PAPBPCPDPEPFf;MFDf:f9PNPIPKPJP2PMP4f1P0M^EW2W0W3W9W8W7W6W1W5W:W;P6P7P8P5P9P:P<P=P>P?P@PAPRPHM>FeMGGg00R[P;%31#1#1#1#3#1#1#5#5#1#1#3#5#H,I3P<%JLD?p,6model0'>1N5?,OG5PLeW4o"). Qed.
End MainDir.
