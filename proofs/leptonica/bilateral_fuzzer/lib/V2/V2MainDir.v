(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibTail SymCall.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec RefMemcpyLib LibWritev PureModel VmLedger AllocIface MemSplit.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import ShapeLawsV2.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MallocLayout V2ExitBase V2Startup V2StartupDefs V2StartupFacts V2MainEntry V2LibStdioCall V2OpenFail_defs V2OpenFail_tail2 V2Open_defs V2Open V2Oom_defs V2MemPreds V2ReadErr V2Malloc65536 V2DirRead_defs V2DirRead V2OpenFailBranch.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import RefNodesFS MuslStrlen RefLayout ArgvEnv StartupTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2MainDir () := "C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec?msg_cannot_openC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec5t_dieC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec>msg_read_errorC5ARocqVerifyHarness?AgentSubmission2V2@V2OpenFailBranchKopen_err_branch_cannot_openK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun7vals_evC5ARocqVerifyHarness?AgentSubmission2V2;V2MainEntry2p0C5ARocqVerifyHarness?AgentSubmission2V2;V2MainEntry2p1C5ARocqVerifyHarness?AgentSubmission2V26V2Open3ENVC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S7regs_okC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission2V26V2Open7out_winC5ARocqVerifyHarness?AgentSubmission2V29V2DirRead>dir_read_errorC5ARocqVerifyHarness?AgentSubmission2V2=V2Malloc65536@malloc65536_nodeC5ARocqVerifyHarness?AgentSubmission2V26V2Open9at_mallocC5ARocqVerifyHarness?AgentSubmission2V26V2OpenAopen_dir_pipelineK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec<t_opened_dirC5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg6t_alt2I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00K47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec8dot_pathI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission2V2;V2Open_defs5o_srBC5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC5ARocqVerifyHarness?AgentSubmission2V2;V2Open_defs5o_knBK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06C5ARocqVerifyHarness?AgentSubmission6Common8PropExec3fx0".
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
  Let ENV := V2Open.ENV a0s path.
  Let model1g := V2Open.model1g sp0 tid brk mbase fs0 stdin0 lim.

  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  (* [comment removed for export] *)
  Hypothesis AL_segs : al_segs = RSEGS.
  Hypothesis AL_rom : al_rom = seg_rom RSEGS.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0x3c370.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x56270.
  Hypothesis AL_glob : forall a, al_globals a -> (0x76568 <= bv_unsigned a < 0x76918)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x77000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x561cc <= bv_unsigned a < 0x561d0)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x77000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x77000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x77000)%Z.
  Hypothesis AL_ret : forall z, In z [0x178bc; 0x178e8; 0x17964; 0x17a64; 0x17b94]%Z -> al_ret_ok (Z_to_bv 64 z).
  Hypothesis AL_env : forall M, V2Malloc65536.env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.

  Let model0 := V2Open.model0 sp0 a0s path envv tid brk mbase fs0 stdin0 lim.

  (* [comment removed for export] *)
  Theorem ref_dir_path :
    path = dot_path ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x17868) mem0 (seg_rom RSEGS)) model0)
             (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)).
Proof.
ltac2:(KReplay.run1 (kr_t_V2MainDir ()) ["MainDir"] "h02HKh12HLh23HOWh32HRh44Hdoth51Mh62P0h72P1h82P2h92P5h:1Rh;4valsp;1p;3p;2p;Bp;4p;Fp;^p;>p;Gp;5p-1p10000p4p710p8g000Gj13Tg000lj17Tg001Jj1:Tg001mj1;Tg002Mj34Tg002gj1MTg0041j28Tg0051j1ATg006:lB@Tg007Nj11Tg0083j2=Tg008_j1<Tg009Aj2STg009aj10Tg00:@j26Tg00;Dj4QTg00<:j4LTg00=0j49Tg00=bj3KTg00?2j4CTg00@Bj3BTg00A8lFDTg00B8l^ETg00C>l>FTg00D6lGGTg00E6j1HTg00ETj2ITg00F:j1JTg00G6j5?Tg00Goj2>Tg00Hdj2NTg00Ikj2OTg00Jfj3PTf0R0#3#3p=5%00#0p=R%00#0#0#0p=2g00KeR1#3R2#5R3#7#:R4#;p,4pathR5g00LJ34p,3AMBR6p,3sp0R7p,3a0sR8P5p,4envvR9p,3tidR:p,5regs0R;p,4mem0R<p,3brkR=p,5mbaseR>p,3fs0R?p,6stdin0R@p,3limRAp,3HvaRBp,3HveRCp,4HvspRDp,4HtidREp,2MERF%M5/8?RG%A5/8?RHP0P6P7P8P5P9P:P;P<P=P>P?P@PAPBPCPDPFp,5HfitsMB@%33#5#7R3#:RI#;%12#7/=I%<4\Ig00MMf2R4,SIg00MlR2#0RJ#0RK#0#RRL#0#2#2#2#2#2#2#2#234f3RM/62=4I7f4R2/6JP7P8P5P9CQ54If5RJ/6KP7P8P5P9CL54If6RK/6L=4I:P6P8P5f7RIC9g00NK;KKg00ODRLP6P8P5f8RNC9PKg00PVCCAB7<IP6p,2ALROp,2CLRPp,3ASRRQP7P8P5P9P:P;P<P=P>P?P@PAPDPEPFp,4Hbrkp,7AL_segsp,6AL_romp,9AL_mallocp,5AL_tpp,7AL_globp,8AL_grantp,8AL_errnop,5AL_rop,5AL_rwp,5AL_hip,6AL_retp,6AL_envg00QORRPHP6POPPPQP7P8P5P9P:P;P<P=P>P?P@PAPBPCPDPEPFf;MFDf:f9PNPIPKPJP2PMP4f1P0M^EW2W0W3W9W8W7W6W1W5W:W;P6P7P8P5P9P:P<P=P>P?P@PAPRPHM>FeMGGg00RGP;%31#1#1#1#1#5#5#1#1#3#1#3#5#H,I3P<%JLD?p,6model0'>1N5?,OG5PLeW4o"). Qed.
End MainDir.
