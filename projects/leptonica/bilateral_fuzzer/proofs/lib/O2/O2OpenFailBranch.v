(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec FileSim RefNodesFS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2Startup O2MainEntry O2OpenFail_defs O2OpenFail O2Open_defs O2Open.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2OpenFailBranch () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC59OSSVerify5KrLib2O2;O2MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open3ENVC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open9above_sp0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2OpenFail6model0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Spec?msg_cannot_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2OpenFailCopenat_errnos_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2OpenFailCref_open_fail_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open6model0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open9model0_OFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open?open_err_branchC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib2O2?O2OpenFail_defs3srAC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3knAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~".
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
    O2Open.open_err_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 lim (t_die (msg_cannot_open path) fs0).
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFailBranch ()) ["Branch"] "h02HKh12HLh22HRh36Haboveh42Heh51Mh62P0h72P1h82P2h93P38h:2P5h;1Rh<1eh=1mh>4valsp;1p;2p;3p;4p;;p;5p;Np;6p;=p10000p4p70g000`R0p4p710R1p8p1001>p4p70P1p8p1001lp4p70P1p8g002bj10Tg003Gj16Tg003ej17Tg004Hj1=Tg004hj12Tg005Mj2UTg0069j1OTg006[j3ATg0072j2?Tg007Rj11Tg0081j34Tg008Kj25Tg009Oj1WTg00:Gj4VTg00;=j4TTg00<3j49Tg00<ej18Tg00=Cj3NTg00=fj1HTg00>mj1BTg00@6j3@Tg00A?j3CTg00BOj4DTg00C_j3ETg00DWl;FTg00EPj2GTg00F6j1>Tg00G2j5ITg00Gkj2JTg00H`j1KTg00Ijj2LTg00Jjj3MTg00Kij2;Tg00LolNPTg00N5l;QTg00Njl;:TP0j6RTg00Obl=STf0R0#1#1p=<%10#1#1#1p=3g00P`R1g00Q>R2#0R3#0#0R4#0#0#0#6R5#7R6#=%23R3#6R7/U6%64#7#O\6f3R4g00Qc5A1g00Re1?64g00SDR4#1R1#1R8#1#<R9#1#3#3#3#3#3#3#3#3R:#134f4R;/54p,3sp0R4546f5/5:f6R<#W54615<1P4p,3a0sR1p,4pathR=p,4envvR>CV546f7R?/58P4P1P=P>CT546f8R8/59p,3tidR9546p,3AMBR6P1P=f9R@C9g00Sc%03#8g00T^5N7#H%B:3@;C8g00U:R:P6P1P=f:R7C9P8g00V`CDp,4mem0R3=E4@g00W[RAP6P4P1P=P>P9p,3brkRBp,5mbaseRCp,3fs0RDp,6stdin0REp,3limRFM;Fg00XQf<RG%22#0#2#2#2#0#0#2#2#0#2#0#0#0#2#0#0#8,G5f;R5%>:DI/J0%K=/LDR25M:X=AP6P4P1P=P>P9p,5regs0P3PBPCPDPEPFp,3Hvap,3Hvep,4Hvspp,2MEp,5Hfitsf=RAPGP5P71;A@P8P?P<P;f2f1P0MNPP6P4P1P=P>P9PBPCPDPEPFM;QP6P4P1P=P>P9PBPCPDPEPFM;:ERW3W0W2W:W8W7W9W6W1W4W5W;W>W<P6P4P1P=P>P9P3PBPCPDPEPFP2M=Seo"). Qed.
End Branch.
