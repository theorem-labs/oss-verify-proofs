(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibTail SymCall.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib LibWritev PureModel VmLedger AllocIface MemSplit.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MallocLayout V23ExitBase V23Startup V23StartupDefs V23StartupFacts V23MainEntry V23LibStdioCall V23OpenFail_defs V23OpenFail_tail2 V23Open_defs V23Open V23Oom_defs V23MemPreds V23ReadErr V23Malloc65536 V23DirRead_defs V23DirRead V23OpenFailBranch.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23MainDir () := "C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec?msg_cannot_openC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec5t_dieC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec>msg_read_errorC5ARocqVerifyHarness?AgentSubmission3V23AV23OpenFailBranchKopen_err_branch_cannot_openK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun7vals_evC5ARocqVerifyHarness?AgentSubmission3V23<V23MainEntry2p0C5ARocqVerifyHarness?AgentSubmission3V23<V23MainEntry2p1C5ARocqVerifyHarness?AgentSubmission3V237V23Open3ENVC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S7regs_okC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission3V237V23Open7out_winC5ARocqVerifyHarness?AgentSubmission3V23:V23DirRead>dir_read_errorC5ARocqVerifyHarness?AgentSubmission3V23>V23Malloc65536@malloc65536_nodeC5ARocqVerifyHarness?AgentSubmission3V237V23Open9at_mallocC5ARocqVerifyHarness?AgentSubmission3V237V23OpenAopen_dir_pipelineK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec<t_opened_dirC5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg6t_alt2I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00K47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec8dot_pathI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission3V23<V23Open_defs5o_srBC5ARocqVerifyHarness@ProcessOversightKTgt_pix_orient_fuzzer_ubsan1M?loaded_segments____________________C5ARocqVerifyHarness?AgentSubmission3V23<V23Open_defs5o_knBK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06C5ARocqVerifyHarness?AgentSubmission6Common8PropExec3fx0".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

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
  Let ENV := V23Open.ENV a0s path.
  Let model1g := V23Open.model1g sp0 tid brk mbase fs0 stdin0 lim.

  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  (* [comment removed for export] *)
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x10e958.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x1381d0.
  Hypothesis AL_glob : forall a, al_globals a -> (0x1584d0 <= bv_unsigned a < 0x158880)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x159000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x13812c <= bv_unsigned a < 0x138130)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x159000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x159000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x159000)%Z.
  Hypothesis AL_ret : forall z, In z [0x63194; 0x631c0; 0x6323c; 0x6333c; 0x6346c]%Z -> al_ret_ok (Z_to_bv 64 z).
  Hypothesis AL_env : forall M, V23Malloc65536.env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.

  Let model0 := V23Open.model0 sp0 a0s path envv tid brk mbase fs0 stdin0 lim.

  (* [comment removed for export] *)
  Theorem ref_dir_path :
    path = dot_path ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x63140) mem0 (seg_rom RSEGS)) model0)
             (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)).
Proof.
ltac2:(KReplay.run1 (kr_t_V23MainDir ()) ["MainDir"] "h02HKh12HLh23HOWh32HRh44Hdoth51Mh62P0h72P1h82P2h92P5h:1Rh;4valsp;1p;3p;2p;Bp;4p;Fp;^p;>p;Gp;5p-1p10000p4p710p8g000Gj13Tg000lj17Tg001Jj1:Tg001mj1;Tg002Mj34Tg002gj1MTg0041j28Tg0051j1ATg006:lB@Tg007Pj15Tg0085j2=Tg008aj1<Tg009Cj2STg009cj10Tg00:Bj26Tg00;Fj4QTg00<>j4LTg00=6j49Tg00=jj3KTg00?:j4CTg00@Jj3BTg00ABlFDTg00BDl^ETg00CLl>FTg00DFlGGTg00EHj1HTg00Efj2ITg00FLj1JTg00GHj5?Tg00HAj2>Tg00I6j2NTg00J=j2OTg00K8j3PTf0R0#3#3p=2%00#0p=R%00#0#0#0p=1g00L7R1#3R2#2R3#7#:R4#;p,4pathR5g00L\34p,3AMBR6p,3sp0R7p,3a0sR8P5p,4envvR9p,3tidR:p,5regs0R;p,4mem0R<p,3brkR=p,5mbaseR>p,3fs0R?p,6stdin0R@p,3limRAp,3HvaRBp,3HveRCp,4HvspRDp,4HtidREp,2MERF%M5/8?RG%A5/8?RHP0P6P7P8P5P9P:P;P<P=P>P?P@PAPBPCPDPFp,5HfitsMB@%33#2#7R3#:RI#;%52#7/=I%<4\Ig00M_f2R4,SIg00N>R2#0RJ#0RK#0#RRL#0#1#1#1#1#1#1#1#134f3RM/62=4I7f4R2/6JP7P8P5P9CQ54If5RJ/6KP7P8P5P9CL54If6RK/6L=4I:P6P8P5f7RIC9g00N];KKg00OXRLP6P8P5f8RNC9PKg00Q?CCAB7<IP6p,2ALROp,2CLRPp,3ASRRQP7P8P5P9P:P;P<P=P>P?P@PAPDPEPFp,4Hbrkp,7AL_segsp,6AL_romp,9AL_mallocp,5AL_tpp,7AL_globp,8AL_grantp,8AL_errnop,5AL_rop,5AL_rwp,5AL_hip,6AL_retp,6AL_envg00R:RRPHP6POPPPQP7P8P5P9P:P;P<P=P>P?P@PAPBPCPDPEPFf;MFDf:f9PNPIPKPJP2PMP4f1P0M^EW2W0W3W9W8W7W6W1W5W:W;P6P7P8P5P9P:P<P=P>P?P@PAPRPHM>FeMGGg00S2P;%51#3#2#5#5#3#2#5#3#5#2#2#2#H,I3P<%JLD?p,6model0'>1N5?,OG5PLeW4o"). Qed.
End MainDir.
