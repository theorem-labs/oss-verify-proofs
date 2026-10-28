(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BCatSim BShapeAlg BazyRestrict BazyRestrictRun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BazyRestrictAlg () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg?node_instr_acctI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I6ARocqVerifyHarness?AgentSubmission3bpB2HF?BazyRestrictRun6dsteps00I6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg8realizes00K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c6ARocqVerifyHarness?AgentSubmission3bpB2HF?BazyRestrictAlg<node_accountC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg:rz_silent1C6ARocqVerifyHarness?AgentSubmission3bpB2HF?BazyRestrictRun:dsteps_indI4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg4TSetI6ARocqVerifyHarness?AgentSubmission3bpB2HF<BazyRestrict8lazy_inv00C6ARocqVerifyHarness?AgentSubmission3bpB2HF<BazyRestrict8restrictI6ARocqVerifyHarness?AgentSubmission3bpB2HF7BCatSim6msteps00C6ARocqVerifyHarness?AgentSubmission3bpB2HF<BazyRestrictEsame_but_materializedC6ARocqVerifyHarness?AgentSubmission3bpB2HF<BazyRestrict=unrestrict_toC6ARocqVerifyHarness?AgentSubmission3bpB2HF?BazyRestrictRun?msteps_restrictI47Corelib4Init5Logic2ex00c6ARocqVerifyHarness?AgentSubmission3bpB2HF?BazyRestrictAlg9rz_dstepsI47Corelib4Init5Logic3and00".
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.

Lemma node_account : forall ms model ms' model',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model').
Proof.
ltac2:(KReplay.run1 (kr_t_BazyRestrictAlg ()) ["WithSegs"] "h05modelh16model'h22msh33ms'p;1p;3p;2p;4p;9g0000j10Tg000Uj1=Tg0013j13Tg001Vj12Tg0028j1<Tg002oj1:Tg003Qj31Tg003kj14Tg0051j25Tg005Qj16Tg006Yj37Tg007Uj48Tg0085j29Tg009=l9;Tg00:BR0g00;IR1g00<?#0#0#0#0#0#0#=#3R2#2R3f2R4#<%:2R231f4R5#4=1321501R2#6p,4segsR3f5R6;75P0P1f3R7P4C8,9231P3p,2SCf6P6P5P7P4f1f0M9;UUUX11X30W0W2o"). Qed.

Lemma rz_dsteps : forall c c' T,
  dsteps segs c c' -> realizes segs c' T -> realizes segs c T.
Proof.
ltac2:(KReplay.run1 (kr_t_BazyRestrictAlg ()) ["WithSegs"] "h01ch11Hh22Hrh32c'h44Hacch52Hhh64Hsvch72IHh81Th92c3h:5modelh;6model'h<2msh=3ms'p;3p;4p;1p;2p;7g00<dj34Tg00=hj41Tg0000j10Tg000Uj15Tg0013j1BTg001Vj1<Tg0028j1;Tg002oj16Tg003Qj33Tg003kj17Tg0051j28Tg005Qj19Tg006Yj3:Tg007Uj4ATg0085j2@Tg00>hj22Tg00?]j7=Tg00@ej7>Tg00Aej7?Tg00BkR0g00C`p,4segsR1f2R2f1R334P1P1p,2SCR4f0R5f3R6C1P1P4P2f4R7C1[X30X00P1P4P5P2C1P5W2X00g00:BR8g00;IR9g00<?#0#0#0#0#0#0#5#BR:#<R;%;6%6:R:33f5R<#7=3;:1889R:#9f6R;=:1<P8P9P7P6CA,@:3312<7=416P1P4P7f:R:C1P1P4f7R=/2;f;R;C1[P1P4P<P;C1P1P4f9R4,2:f8R1/2=f<P:P4P1P=P<P7P6F=P3P5O1F>W2W7W1W4W6W5X90X;9X=8W:W<P6P2P5F?W1W8X30W0o"). Qed.

Lemma rz_account_step : forall ms model ms' model' T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  realizes segs (mkCfg ms' model') T ->
  realizes segs (mkCfg ms model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_BazyRestrictAlg ()) ["WithSegs"] "h04Hacch12Hhh22Hrh34Hsvch41Th55modelh66model'h72msh83ms'p;1p;3p;2p;4p;7g0000j10Tg000Uj1@Tg0013j14Tg001Vj13Tg0028j1?Tg002oj1;Tg003Qj31Tg003kj15Tg0051j26Tg005Qj17Tg006Yj38Tg007Uj49Tg0085j2:Tg00>hj22Tg00=hj4>Tg00?]j7=Tg00@ej7<Tg00:BR0g00;IR1g00C`g00<?#0#0#0#0#0#0#@#4R2#3R3f3R4#?%;2R231f5R5#5=1321601R2#7p,4segsR3f6R6;85P0P1f4R7P4C9,:231P3p,2SCR21257P4C>P3P2f8R2f7R3'21265P7P2P3P6P5P4f2f1F=f0F<W2W0W3W1W4X61X80W5W7o"). Qed.

Section WithLazy.
Variables L S : list (word * word).
Hypothesis HL : lazy_ranges_okb segs L = true.

Theorem rz_msteps_lazy : forall msF ms1 model T,
  lazy_inv L S model ->
  m_halted model = None ->
  msteps segs (restrict L S msF) ms1 ->
  (forall model', lazy_inv L S model' -> same_but_materialized model model' ->
     m_halted model' = None ->
     restrict L S (unrestrict_to L S msF ms1) = ms1 ->
     realizes segs (mkCfg (unrestrict_to L S msF ms1) model') T) ->
  realizes segs (mkCfg msF model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_BazyRestrictAlg ()) ["WithSegs"; "WithLazy"] "p'0h01Hh16model'h22Hdh32Hhh43Hh'h54Hinvh65Hinv'h72Hkh83Hmsh92Hrh:5Hsameh;1Th<1eh=5modelh>3ms1h?3msFi001xp;3p;1p;2p;4p;:p;5g00DZj39Tg0000j17Tg000Uj1ATg0013j1?Tg001Vj1GTg002oj1ETg00E]j3;Tg00F^j3@Tg00GZj24Tg00Hhj41Tg00>hj20Tg00=hj46Tg00Inl:FTg00<dj38Tg00K9R0j2DTg00KSj5CTg0028j1BTg003Qj3<Tg00LXR1j2>Tf2R2f1R3#Bf0R43<p=2g00:BR5f3R6?;23;<4p=51>34,>2p=3A<534,>2p=:f5R7f4R8P6P2P3P4C13;p==g00;IR9g00C`p,1LR:p,1SR;;93R<g00<?#7#7#7#7#7#7#A#?R=#GR>%E=R=722R?p,4segsR@A;:;7;@8A9:;4RAf6RB/43P:P;P:P;f:RCf9RDC1PDC5P@p,2SCREP:P;f;RFPCC1RG/08f8RHC6[\?[[^19P@P:P;p,2HLf7R?PBP7P6P2P3M:F10HBP:P;PHP?C1R2/0458@14B4A2>4=RIP:P;P2P?C53373AX19,D9P0P910D?R0P:P;PDPHC1R2/0458@14?4P:P;P2PHC573I73AX19P@PEP0PBC6P410FD10G458@14D4P:P;PGPCC573I73AP1f<RA/0CP:P;PAPFC1RI/0358@14C3A2>3=A;:;I;:F53<P@PEf=R</0FPCC6P4f>RC/0AP:P;PCP<C1/0658@A9:;814<8A2>8=P:P;P:P;f?R8PCE=;:C33P1A9:;714C7A2>7=P:P;P:P;f@P8C1P8C533P@PEfAR6/08PCC6P4A9:;?146HA2>H=P:P;P:P;fCRHfBR?C1P?C533P114?DA2>D=P:P;P:P;fDRCPHE=;:HP@PEfERI/0HP?C6P414CFA2>A=P:P;P:P;fGRAfFRCE=;:CP1A2><=P:P;P:P;fHPAC1PAC5P@PEfIRE/0APCC6P4A2>8=P:P;P:P;fKR8fJR=C1P=C5fLR>/0=P:P;P>P8C1/06PEP<PIP6PDP7P3P4O5DCW9W4P3P4O2n2001000000120000000W0W:P3P4O2n2001000000120000000W0W6P3P4O2n2001000000121000000W0W2P3P4O2n2001000000121000000W0X19P3P4O2n2001000000121100000b<W7W8W3W5W;W=X>5X?5o"). Qed.

End WithLazy.
End WithSegs.
