(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's mmap base; the model's channel reader as a premise of the writes; recorded proofs re-encoded or written as text where the change reaches them). *)
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
    (* LPS 75d69e00: [main_entry] takes the run's whole ProcInput and the mmap base
     in place of (argv, envp, uid, hwcap).  [mkProcInputC] (Amb.v:42) is the very
     input this Section's own conclusion runs -- [in_argv]/[in_envp]/[in_uid]/
     [in_hwcap] of it reduce to exactly the four the old spelling named -- so
     naming it here is the same statement, not a narrower one. *)
  Local Notation INP := (mkProcInputC [a0s; path] envv fs0 stdin0) (only parsing).
  Hypothesis ME : main_entry sp0 rdraw INP mbase tid regs0 mem0.
  (* LPS 727298f3: the launch's channel reader ([Run.valid_input]); the writes below need it *)
  Hypothesis Hrdr : a_channel_reader = true.

  Theorem open_err_branch_cannot_open :
    S1RFront.open_err_branch sp0 a0s path envv tid rdraw mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open path) fs0).
Proof.
ltac2:(KReplay.run1 (kr_t_S1OpenFailBranch ()) ["FXALL"; "Branch"] "p%0p'0p%1p'1p%2p'2p%3p'3p%4p'4p%5p'5p%6p'6p%7p'7p%8p'8p%9p'9p%:p':p%;p';p%<p'<p%=p'=p%>p'>p%?p'?p%@p'@p%Ap'Ap%Bp'Bp%Cp'Cp%Dp'Dp%Ep'Ep%Fp'Fp%Gp'Gp%Hp'Hp%Ip'Ip%Jp'Jp%Kp'Kp%Lp'Lp%Mp'Mp%Np'Np%Op'Op%Pp'Pp%Qp'Qp%Rp'Rp%Sp'Sp%Tp'Tp%Up'Up%Vp'Vp%Wp'Wp%Xp'Xp%Yp'Yp%Zp'Zp%[p'[p%\p'\p%]p']p%^p'^p%_p'_p%`p'`p%ap'ap%bp'bp%cp'cp%dp'dp%ep'ep%fp'fp%gp'gp%hp'hp%ip'ip%jp'jp%kp'kp%lp'lp%mp'mp%np'np%op'op%pp'pp%qp'qp%rp'rp%sp'sp%tp'tp%up'up%vp'vp%wp'wp%xp'xp%yp'yp%zp'zp%{p'{p%|p'|p%}p'}p%~p'~g00Geg001Vg0013g000Ug0000g0000g0000g0000g0000g0000g00HCO1O1O1S02O1O1O1O1S01O1S00O1g002[g000Ug0026g0000g00HCO1O1S04O1S03Q00O2Q00g003Gg0013g000UQ02O1O1O1S05pB1000g003ig00Gef3g00HhO3g005?g00Ijg004@Q00f3O2g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g004`g00JIO1O1S08O1O1O1S07O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1O1S06O1O3g005?Q00g005Yf4g00JIO2p,3sp0O3g005?Q00g005Yf5Q06O2g006Lf6O1O3g005?Q00g005Yf6g004`g00JIO1O2g007Dp,3AMBp,3a0sp,4pathp,4envvp,5rdrawO5O3g005?Q00g005Yf7Q08O2g008;p,3AMBp,3a0sp,4pathp,4envvp,5rdrawO5O3g005?Q00g005Yf8Q07O2p,3tidO3g00=Ng0092p,3a0sp,4pathf9O3g00<Vg00Jhg00:hg00:EQ03g009gg0000Q04O1O1g00KdO3O1g00;^Q06O1O3f8O3g00>Mg00L@g0092p,3a0sp,4pathf:O3f8g00N5O4Q00g00@6g00?LQ01p,3sp0O2g00?LQ01f0O2O2g005?Q05f;f1O1p,4mem0f1O1O3pB1000i001xpB1100g00Adg00L@g0092p,3a0sp,4pathf<O3f:g00N5g00O1f1g00@Rg00Omg00PMO2g005?g00Omg00@lg00L@g00N5g00O1O3g00PMO3dO7g00>Mg00L@g0092p,3a0sp,4pathf<O3f:g00O1O4g00Cip,2fxp,3AMBp,3sp0p,3a0sp,4pathp,4envvp,3tidp,5rdrawp,5regs0p,4mem0p,3brkp,5mbasep,3fs0p,6stdin0g00Pmp,3Hvap,3Hvep,4Hvspp,2MEp,4Hrdrf>f=f<f;g00Bbf>f:O2f9f8f7f5f3f0f1OPi003HK'pB2100i006HabovepB0100i002HKpB0100i002HRpB0100i002P5pB0100i002P2pB0100i002P1pB0100i003P38pB0100i002P0pB0100i002HLpB0100i002HepB0100i001MpB0100i001RpB0100i004valspB0100i001epB0100g00Fdp,2fxp,3AMBp,3sp0p,3a0sp,4pathp,4envvp,3tidp,5rdrawp,4mem0p,3brkp,5mbasep,3fs0p,6stdin0g00Eog00E0p,4pathO1p,3fs0O2O>eo"). Qed.
End Branch.

End FXALL.
