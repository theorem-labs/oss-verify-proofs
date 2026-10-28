(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BSimInv BExitSim BShapeAlg BReach BFrame BazyRestrict BazyRestrictRun BazyRestrictAlg BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BsLazyRun () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I6ARocqVerifyHarness?AgentSubmission3bpB2HF6BazySR4lzok00C6ARocqVerifyHarness?AgentSubmission3bpB2HF<BazyRestrict8restrictI6ARocqVerifyHarness?AgentSubmission3bpB2HF7BCatSim6msteps00C6ARocqVerifyHarness?AgentSubmission3bpB2HF<BazyRestrictEsame_but_materializedC6ARocqVerifyHarness?AgentSubmission3bpB2HF6BazySR8hid_sameC6ARocqVerifyHarness?AgentSubmission3bpB2HF6BazySR;lzok_rangesC6ARocqVerifyHarness?AgentSubmission3bpB2HF6BazySR8lzok_invC6ARocqVerifyHarness?AgentSubmission3bpB2HF6BazySR;lzok_haltedC6ARocqVerifyHarness?AgentSubmission3bpB2HF?BazyRestrictRun?msteps_restrictC6ARocqVerifyHarness?AgentSubmission3bpB2HF<BazyRestrict=unrestrict_toI6ARocqVerifyHarness?AgentSubmission3bpB2HF?BazyRestrictRun6dsteps00I6ARocqVerifyHarness?AgentSubmission3bpB2HF<BazyRestrict8lazy_inv00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2ex00C6ARocqVerifyHarness?AgentSubmission3bpB2HF6BazySRChid_same_unrestrictC6ARocqVerifyHarness?AgentSubmission3bpB2HF6BazySR;lzok_liftedC6ARocqVerifyHarness?AgentSubmission3bpB2HF?BazyRestrictAlg9rz_dstepsI47Corelib4Init5Logic2eq00I6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg8realizes00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI47Corelib4Init5Logic3and00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C6ARocqVerifyHarness?AgentSubmission3bpB2HF4Bcfg=hunspell_scfgI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg4TSetK47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums8positive01C6ARocqVerifyHarness?AgentSubmission3bpB2HF9BPropExec4mkstc6ARocqVerifyHarness?AgentSubmission3bpB3Drv9BsLazyRun>rz_msteps_lazy".
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WithSegs.
  Context {fx : DFP}.
Variable segs : list Segment.
Variables L S Zr : list (word * word).

Theorem rz_msteps_lazy : forall msF ms1 mo T,
  lzok segs L S Zr (mkCfg msF mo) ->
  msteps segs (restrict L S msF) ms1 ->
  (forall msF' mo',
     lzok segs L S Zr (mkCfg msF' mo') ->
     same_but_materialized mo mo' ->
     hid_same L S msF msF' ->
     restrict L S msF' = ms1 ->
     realizes segs (mkCfg msF' mo') T) ->
  realizes segs (mkCfg msF mo) T.
Proof.
ltac2:(KReplay.run1 (kr_t_BsLazyRun ()) ["WithSegs"] "p'0h01Hh13mo'h26model'h35Hconth42Hdh53Hh'h65Hinv'h73Hmsh83Hokh96Hrestrh:5Hsameh;1Th<1eh=2moh>3ms1h?3msFh@4msF'i001xp;2p;5p;3p;4p;6p;:p;1p;<p;7p10000p4p7210p1000\p4p710p8g001:j20Tg001oj5>Tg002hj37Tg003ij3ATg004ej23Tg0063j4OTg006nj6CTg007lj6BTg008gj6@Tg009el:?Tg00;0j41Tg00<6j3:Tg00=:j39Tg00>=j18Tg00>bj1NTg00?@j1MTg00?cj1LTg00@Ej1HTg00@gR0j2DTg00AAj4ETg00BGl<FTg00CEj7GTg00DJj3;Tg00Ddj4JTg00Edj1KTg00F[R1j2=Tg00G6R2f1R3f0R43;p=If2R5g00H=R6P3P4CJp=6%K3=;54p=4f3R7?753=;24p=51=34,=5p=2A;234,=5p=<g00I;R8g00J1p,4segsR9p,1LR:p,1SR;p,2ZrR<1073D>f4R=97:;R>=A97P9P:P;P<1034D>f6R?/33P:P;f9R@P7CO1I>@f5R>/0=f8RA569[[[[^18^@2P9P:P;P9P:P;P<10?=RBP5ECP?P>P=P9P:P;P<PBP5EBP9P:P;P<PBP5E@P3M:?f7R5/0>P:P;P5P?C1RB/045:9A9:;4RC13>4g00Jk#8#8#8#8#8#8#N#MRD#LRE%HDRD744RFP:P;PBP?C53232X28,D8P0P810A?R0P:P;PAP5C1RB/045:913?4P:P;PBP5C572F72CX28A690>P4f:R0/0AP:P;P0P@C1RB/045:913A4P:P;PBP@C572F72CP1f;RC/0@P:P;PCP0C1RF/035:9A9:;313@3A4E3DA7:;F;<032f<RF/00=69@P4f=R0/0CP:P;P0PFC1/075:9A9:;=13F=A4E=DP:P;f>R=P0C197:;;<032P1A9:;>130>A4E>DP:P;P:P;f?R7P=C1P=C532f@RB/0==690P4A9:;513BAA4EADP:P;P:P;fBRAfARBC1PBC532P113B@A4E@DP:P;fCR5PAC197:;;<AfD/0A=69BP4135CA4EFDP:P;fFRFfER5C197:;;<5P1A4E0DP:P;P:P;fGR1PFC1PFC5fHRC/0F=695P4A4E7DP:P;P:P;fJR7fIRDC1PDC5P9P6fKR6/0DP:P;P6P7C1RE/0BPCP0P5PEPBP9P:P;P<P6PDPEPBP1P@P>P:P;P6P7CER7M<FP>P7P4O6FGW9W5P3P4O2n2001000000120000000W0W:P3P4O2n2001000000120000000W0W6P3P4O2n2001000000121000000W0W4P3P4O2n2001000000121000000W0X18P3P4O2n2001000000121100000b<W3W7W8W;W=X>2X?2o"). Qed.

Corollary rz_msteps_lazy_mkst : forall msF regs pc mem rom regs' pc' mem' mo T,
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem rom ->
  msteps segs (mkst regs pc mem rom) (mkst regs' pc' mem' rom) ->
  (forall msF' mo',
     lzok segs L S Zr (mkCfg msF' mo') ->
     same_but_materialized mo mo' ->
     hid_same L S msF msF' ->
     restrict L S msF' = mkst regs' pc' mem' rom ->
     realizes segs (mkCfg msF' mo') T) ->
  realizes segs (mkCfg msF mo) T.
Proof.
ltac2:(KReplay.run1 (kr_t_BsLazyRun ()) ["WithSegs"] "h05Hconth13Hmsh23Hokh32Hrh41Th51mh63memh74mem'h82moh93mo'h:3msFh;4msF'h<2pch=3pc'h>4regsh?5regs'h@3romp;1p;2p;5p;3p;4p;6p;7g00>=j11Tg00KPj1@Tg00>bj13Tg00?@j18Tg0000j2?Tg00?cj1:Tg001:j24Tg001oj56Tg002hj32Tg00L5j50Tg00DJj35Tg003ij37Tg004ej29Tg0063j4>Tg00Ddj4=Tg000\j6;Tg00Loj7<Tg00G6R0g00Jk#1R1#@#3%11#1R1#1#1#1#3#8R2'?R3%31#8#:\2R1g00I;R4g00J1p,4segsR5p,1LR6p,1SR7p,2ZrR8f9R9f1R:'4D6f:R;9267p,2fxR<P9f8R=f7R>f6R?D0550P<P;P9P=P>D0P<P?f5R@f4RAP>D0575P5P6P7P8f0R8,4:D619>:P6P7f@f3RBC>A267AP<f<RCf;RDP;f=RED0550P5g00H=14@AP9C=[[[[^94^;0PEP<P=P>P?P9D0P@PAPBP0P<PCPDP;P9D0P<P9P=P>P;D09758X50P:A267Ef2E;P8F<W0W1W3W2W4W8X71X=2X?3X@1W6X<2W>W:o"). Qed.
End WithSegs.
