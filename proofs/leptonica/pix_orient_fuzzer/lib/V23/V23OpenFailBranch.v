(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec FileSim RefNodesFS.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Startup V23MainEntry V23OpenFail_defs V23OpenFail V23Open_defs V23Open.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23OpenFailBranch () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun7vals_evC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC5ARocqVerifyHarness?AgentSubmission3V23<V23MainEntry2p0C5ARocqVerifyHarness?AgentSubmission3V23<V23MainEntry2p1C5ARocqVerifyHarness?AgentSubmission3V237V23Open3ENVK47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24ridxK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sr_updC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S7regs_okC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver=SymExec2Sound4SX2S7know_okC5ARocqVerifyHarness?AgentSubmission3V237V23Open9above_sp0C5ARocqVerifyHarness?AgentSubmission3V23;V23OpenFail6model0C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec?msg_cannot_openC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver4Spec5t_dieI5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00C5ARocqVerifyHarness?AgentSubmission3V23;V23OpenFailCopenat_errnos_rangeC5ARocqVerifyHarness?AgentSubmission3V23;V23OpenFailCref_open_fail_errnoC5ARocqVerifyHarness?AgentSubmission3V237V23Open6model0C5ARocqVerifyHarness?AgentSubmission3V237V23Open9model0_OFC5ARocqVerifyHarness?AgentSubmission3V237V23Open?open_err_branchI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3srAK47Corelib4Init5Logic4True01C5ARocqVerifyHarness@ProcessOversightKTgt_pix_orient_fuzzer_ubsan1M?loaded_segments____________________C5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3knAI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission6Common8PropExec3fx0".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Section Branch.
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
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.

  Theorem open_err_branch_cannot_open :
    V23Open.open_err_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 lim (t_die (msg_cannot_open path) fs0).
Proof.
ltac2:(KReplay.run1 (kr_t_V23OpenFailBranch ()) ["Branch"] "h02HKh12HLh22HRh36Haboveh42Heh51Mh62P0h72P1h82P2h93P38h:2P5h;1Rh<1eh=1mh>4valsp;1p;2p;3p;4p;;p;5p;Np;6p;=p10000p4p70g000`R0p4p710R1p8p1001>p4p70P1p8p1001lp4p70P1p8g002bj10Tg003Gj17Tg003ej18Tg004Hj1>Tg004hj16Tg005Mj2UTg0069j1OTg006[j3BTg0072j2@Tg007Rj11Tg0081j34Tg008Kj25Tg009Oj1WTg00:Gj4VTg00;?j4TTg00<7j4:Tg00<kj19Tg00=Ij3NTg00=lj1HTg00?3j1GTg00@<j3ATg00AEj3CTg00BUj4DTg00Cej3ETg00D_l;FTg00EZj2?Tg00F@j1ITg00G<j5JTg00H5j2KTg00Hjj1LTg00J4j2MTg00K4j3<Tg00L3j2PTg00M;lNQTg00NCl;;Tg00O:l;RTP0j6STg00P4l=XTf0R0#1#1p==%10#1#1#1p=2%60#6p=3g00Q4R1g00QRR2#0R3#0#0R4#0#0#0#7R5#8R6#>%63R3#7R7/U6%74#8#O\6f3R4g00R75B1g00S91@64g00SXR4#1R1#1R8#1#=R9#1#2#2#2#2#2#2#2#2R:#134f4R;/54p,3sp0R4546f5/5:f6R<#W54615<1P4p,3a0sR1p,4pathR=p,4envvR>CV546f7R?/58P4P1P=P>CT546f8R8/59p,3tidR9546p,3AMBR6P1P=f9R@C:g00T7%03#9g00U45N7#H%G:3A;C8g00UPR:P6P1P=f:R7C:P8g00W7CDp,4mem0R3=E4@g00X4RAP6P4P1P=P>P9p,3brkRBp,5mbaseRCp,3fs0RDp,6stdin0REp,3limRFM;Fg00Xjf<RG%02#0#0#3#3#0#3#3#3#3#0#6#0#0#9,?5f;R5%I:DJ/K0%L=/MDR25<:X=AP6P4P1P=P>P9p,5regs0P3PBPCPDPEPFp,3Hvap,3Hvep,4Hvspp,2MEp,5Hfitsf=RAPGP5P71PA@P8P?P<P;f2f1P0MNQP6P4P1P=P>P9PBPCPDPEPFM;;P6P4P1P=P>P9PBPCPDPEPFM;RESW3W0W2W:W8W7W9W6W1W4W5W;W>W<P6P4P1P=P>P9P3PBPCPDPEPFP2M=Xeo"). Qed.
End Branch.
