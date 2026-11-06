(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg SymExec Frame RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DivergeSim SRealizes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_SymDriveS2 () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K59OSSVerify5KrLib8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9scs_denotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I49OSSVerify5KrLib9SRealizes9srealizes00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6SymRun9run_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib6CatSim6msteps00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C49OSSVerify5KrLib6SymRun;carry_afterC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C49OSSVerify5KrLib9SRealizes:srz_mstepsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00I59OSSVerify5KrLib8SymExec23SX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C49OSSVerify5KrLib8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Section Drive.
Context {fx : FPState}.
Variable segs : list Segment.

Theorem srz_run : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R model T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     srealizes segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  srealizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveS2 ()) ["Drive"] "p'0h01Rh11Hh22R'h31Eh42HKh52HRh63HR'h72Hch85Hconth93Hexh:2Hhh;5Hlazyh<3Hlfh=3Hmsh>3Hsch?4Hsc2h@1MhA2M'hB1ThC1ehD4fuelhE3hs2hF2knhG3kn'hH5modelhI2nxhJ2pchK3romhL3scrhM4scr'hN3scshO4scs2hP2srhQ3ss'hR5stopsi001xp;1p;2p;5p;7p;4p;3p;Dp;=p;9g0000j18Tg000Pj19Tg0015j1BTg001Sj1DTg0026j1GTg002Xj1TTg003=j2RTg003ij2;Tg004Ij1>Tg004ij5KTg005fj7JTg006`j4@Tg007@j3<Tg007Zj11Tg008Qj3UTg009Hj35Tg00:Gj4FTg00;Fj4ETg00<Gj1STg00=>j1QTg00=`j1NTg00>Xj1:Tg00?Pj32Tg00@Qj5ATg00ACj2?Tg00B8j3=Tg00C2lDLTg00Cgj26Tg00Dgj13Tg00E]j37Tg00FQR0j24Tg00FlR1j2ITg00GFl=HTg00H=j2OTg00HWl9PTg00IPj2CTf1R2f0R3#3'Cp=Mf5R4f4R5f3R6f2R7'CP2P3DAp=0g00J6R8g00JUR9#8g00K3R:g00Kn#8g00Lf#8R;g00M`R<g00N]R=#8R>g00OYR?#8R@g00P9g00Q0#9RA#9#9RB#9#9#9#BRC#DRD%BB#D#G[RB%TA#B/RDRAg00QUg00RK1;<>RE/;:p,4segsRFfBRGg00S=fARHf@RIf?RJf>RKg00S]#>f=RLf<RMDK%>=FJPEP:P<P>f;R<f:REC@f9R=C@3<1;;>RN/;@%1M%>?R?7UKPNP@P;P>P=f8R@C@f7RNC@3<A5NI5PFP@PNPICFPFP@P=PKCEPFP=PEPMCE%GD%SN%QD3<1;DDRD#8%N@%>D3<fERD#:RN=5J2PFPIP2fCRECFfGRO#192HI9<B7p,2fxR7P5fHRP,MCRQP6PIDA/?K==FL[[[^AB^2AP7PFfKRRfJRSfIRTPPPOfFRUPDfDRVPEPGPKPLPMP<P@f6P4P5MDLA5JN3%1DRN,6JP7PMPCPTPKPLE0P7P3PC%3DA2JKNPLE057F'4'4X0A,IAP1PA%:U=5I3%1UR1,6IP7PLPCPSPJPKE0RNP7P3PC%3UA2IJ1PKE057F'4'4X0A1?NM==F<P3%:P=5G3%1PR<,6GP7PJPCfLRNPHPIE0P7P3PQA2GH<PIDA57F'4'4P0%:T=5E2%1TR<,6EP7PIPCfMRQPGPHE0P7P2PC%3TA2EG<PHE057F'4P7PHPCfNRHPEPGE0/?I==FJP3%:R=5D6%1NR6,6UP7PEPCfPR<PDPVE0P7P5PC%3NA2UD6PVE057F'4P0%1QR0,6OP7PVPCfQR6PUPDE0P7P4PC%3QA2OU0PDE057FP7PDPCfRPOPUE0/?V==FEP3fO#1,6TP7POPCfTPTPPE0P7P@PC%3<%1<92STPPE057FPFP7PPPCfUPSPTE0P7P=PC%36%16R692RSRCPTE0POPUPJPKP3PLP=PCP4PFPRPSP6fSP?PHPQPNPVP2PGPIM=H1OBCO5M9PW=W<P2P3O2n2001000000120000000W1W6P2P3O2n2001000000121000000W1X2AP2P3O2n2001000000121100000bCW8W;W:W?W>W4W5W7W9WBWHW0XKBW@W3WEXO>XG;XM:WNWQXI8WFWPXJ9WLWRWDo"). Qed.
End Drive.

Ltac run_block_with_s HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- srealizes _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (srz_run segs fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | try reflexivity; try assumption
            | try reflexivity; try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
              intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]
          end
        end
      end
    end
  end.

Tactic Notation "run_block_gen_s" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with_s HR HK fuel stops scr NX keep
  end.
