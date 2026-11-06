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
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec FileSim RefNodesFS.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Startup O23MainEntry O23OpenFail_defs O23OpenFail O23Open_defs O23Open.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23OpenFailBranch () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC59OSSVerify5KrLib3O23<O23MainEntry2p0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23MainEntry2p1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open3ENVC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open9above_sp0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23OpenFail6model0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib6Common9CliDriver4Spec?msg_cannot_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23OpenFailCopenat_errnos_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23OpenFailCref_open_fail_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open6model0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open9model0_OFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Open?open_err_branchC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib3O23@O23OpenFail_defs3srAC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs3knAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~".
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
    O23Open.open_err_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 lim (t_die (msg_cannot_open path) fs0).
Proof.
ltac2:(KReplay.run1 (kr_t_O23OpenFailBranch ()) ["Branch"] "h02HKh12HLh22HRh36Haboveh42Heh51Mh62P0h72P1h82P2h93P38h:2P5h;1Rh<1eh=1mh>4valsp;1p;2p;3p;4p;;p;5p;Np;6p;=p10000p4p70g000`R0p4p710R1p8p1001>p4p70P1p8p1001lp4p70P1p8g002bj11Tg003Gj17Tg003ej19Tg004Hj1XTg004hj12Tg005Mj2MTg0069j1BTg006[j3@Tg0072j2?Tg007Rj10Tg0081j34Tg008Kj26Tg009Oj1VTg00:Gj4UTg00;?j4TTg00<7j4:Tg00<kj18Tg00=Ij3LTg00=lj1KTg00?3j1ATg00@<j3CTg00AEj3DTg00BUj4ETg00Cej3FTg00D_l;GTg00EZj2HTg00F@j1ITg00G<j5JTg00H5j2>Tg00Hjj1=Tg00J4j2NTg00K4j3OTg00L3j2PTg00M;lNQTg00NCl;;Tg00O:l;RTP0j6STg00P4l=WTf0R0#1#1p=5%00#0p=<%00#0#0#0p=3g00Q4R1g00QRR2#1R3#5R4#1#5#7R5#9R6#X%23R3#7R7/M6%74#9#B\6f3R4g00R75@1g00S91?64g00SXR4#0R1#0R8#0#<R9#0#3#3#3#3#3#3#3#3R:#034f4R;/64p,3sp0R4546f5/6:f6R<#V54616<1P4p,3a0sR1p,4pathR=p,4envvR>CU546f7R?/68P4P1P=P>CT546f8R8/69p,3tidR9546p,3AMBR6P1P=f9R@C:g00T7%13#8g00U45L7#K%A:3C;D8g00UPR:P6P1P=f:R7C:P8g00W7CEp,4mem0R3=F4@g00X4RAP6P4P1P=P>P9p,3brkRBp,5mbaseRCp,3fs0RDp,6stdin0REp,3limRFM;Gg00Xjf<RG%52#5#2#1#2#1#2#1#2#2#1#2#1#2#5#5#8,H5f;R5%I:DJ/>0%==/NDR25O:X=AP6P4P1P=P>P9p,5regs0P3PBPCPDPEPFp,3Hvap,3Hvep,4Hvspp,2MEp,5Hfitsf=RAPGP5P71PA@P8P?P<P;f2f1P0MNQP6P4P1P=P>P9PBPCPDPEPFM;;P6P4P1P=P>P9PBPCPDPEPFM;RESW3W0W2W:W8W7W9W6W1W4W5W;W>W<P6P4P1P=P>P9P3PBPCPDPEPFP2M=Weo"). Qed.
End Branch.
