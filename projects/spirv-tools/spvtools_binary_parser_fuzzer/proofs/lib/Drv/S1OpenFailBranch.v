(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SymXfer Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SRealizes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1Spec S1Start S1BootDefs S1MainEntry S1OpenFail_defs S1OpenFail S1PilotOOM_defs S1RFront.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1OpenFailBranch () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00C49OSSVerify5KrLib6SymRun7vals_evC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC59OSSVerify5KrLib3Drv;S1MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv;S1MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv8S1RFront3ENVC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2eq01C49OSSVerify5KrLib7SymXfer;kderive_allC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7SymXferAkderive_all_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1OpenFailCopenat_errnos_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:S1OpenFailCref_open_fail_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv6S1Spec?msg_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv6S1Spec5t_dieC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv8S1RFront?open_err_branchC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib3Drv?S1PilotOOM_defs3srAC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify6KrSpec8ProblemscSrc_spirv_tools_spvtools_binary_parser_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?S1PilotOOM_defs3knAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv?S1OpenFail_defs3knAC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3Drv8S1RFront3LIMC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Section FXALL.
Context {fx : FPState}.

Section Branch.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rdraw : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 rdraw [a0s; path] envv a_uid a_hwcap tid regs0 mem0.

  Theorem open_err_branch_cannot_open :
    S1RFront.open_err_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open path) fs0).
Proof.
ltac2:(KReplay.run1 (kr_t_S1OpenFailBranch ()) ["FXALL"; "Branch"] "h02HKh13HK'h22HLh32HRh46Haboveh52Heh61Mh72P0h82P1h92P2h:3P38h;2P5h<1Rh=1eh>4valsh?1xp;1p;2p;3p;4p;7p;Op;=g0000j13Tg000Uj16Tg0013j17Tg001Vj1<Tg0026j1RTg002[j2OTg003Gj1ETg003ij3@Tg004@j2>Tg004`j10Tg005?j31Tg005Yj24Tg006Lj1QTg007Dj4PTg008;j4NTg0092j35Tg009gj1HTg00:Ej3DTg00:hj1BTg00;^j1ATg00<Vj3?Tg00=Nj3CTg00>Mj48Tg00?Lj29Tg00@6j2FTg00@Rj2GTg00@lj3=Tg00Adj7ITg00Bbj2JTg00CilOKTg00E0j1LTg00Eoj2MTg00Fdl=:Tf0R0#0#0p=;%00#0#0#0p=2g00GeR1g00HC#3R2#3#3R3#3#3#3#6R4#7R5#<%R2R2#6R6/O5%63#7#ER3\5f3R7g00Hh5@1g00Ij1>57g00JIR1#0R8#0R9#0#;R:#0#2#2#2#2#2#2#2#2R;#031f4/41p,3sp0R1515f5R</4;f6R=#Q51514=8P1p,3a0sR=p,4pathR8p,4envvR>CP515f7R?/49P1P=P8P>CN515f8R9/4:p,3tidR:515f9R@95=8g00Jh%32#Hg00Kd5D6#B%A;3?;C9g00L@R;f:R695=8P9g00N5R2C819411940'Ff;R4f1RAO1p,4mem0RBPAO1513[^?5P;f<R595=8R3P6P2g00O1RCPAg00OmRDg00PMRE'GA=;2C=1DEdFIP;P3P6PCC8p,2fxRCp,3AMBR3P1P=P8P>P:p,5rdrawp,5regs0PBp,3brkR;p,5mbaseREp,3fs0RDp,6stdin0R2g00Pmp,3Hvap,3Hvep,4Hvspp,2MEf>RFf=P5P41JF6P@P9P?P<P7P0PAMOKb1W4W0W3W;W9W8W:W7W2W5W6W<W>W=PCP3P1P=P8P>P:PBP;PEPDP2%L8/MDM=:eo"). Qed.
End Branch.

End FXALL.
