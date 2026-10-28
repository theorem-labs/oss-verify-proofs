(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BSimInv BExitSim BCatSim BShapeAlg.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BReach () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init6Specif9proj1_sigC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufk6ARocqVerifyHarness?AgentSubmission3bpB2HF6BReach6sreach01I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00i6ARocqVerifyHarness?AgentSubmission3bpB2HF6BReach6sreach00K47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00k6ARocqVerifyHarness?AgentSubmission3bpB2HF6BReach6sreach02c6ARocqVerifyHarness?AgentSubmission3bpB2HF6BReach:sreach_indI4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00C6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg7node_okC6ARocqVerifyHarness?AgentSubmission3bpB2HF4Bcfg8the_scfgI4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01c6ARocqVerifyHarness?AgentSubmission3bpB2HF6BReach;sreach_nodeI47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg:node_instrc6ARocqVerifyHarness?AgentSubmission3bpB2HF6BReach>sreach_silent1I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I6ARocqVerifyHarness?AgentSubmission3bpB2HF7BCatSim6msteps00c6ARocqVerifyHarness?AgentSubmission3bpB2HF6BReach<sreach_step1C6ARocqVerifyHarness?AgentSubmission3bpB2HF7BCatSim:msteps_indK47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission3bpB2HF8BExitSim:is_exit_noC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg6t_exitc6ARocqVerifyHarness?AgentSubmission3bpB2HF6BReach=sreach_mstepsI6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg8realizes00C6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg7rz_exitc6ARocqVerifyHarness?AgentSubmission3bpB2HF6BReach?sreach_realizesK47Corelib4Init9Datatypes3nat01".
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.

Let sstepc := sstep_cfg segs the_scfg.

Inductive sreach (Q : config -> Prop) : config -> Prop :=
| sr_done : forall c, Q c -> sreach Q c
| sr_step : forall c,
    (exists c', sstepc c [] (SNext c')) ->
    (forall evs X, sstepc c evs X -> evs = [] /\ exists c', X = SNext c') ->
    (forall evs c', sstepc c evs (SNext c') -> sreach Q c') ->
    sreach Q c.

Lemma sreach_done : forall (Q : config -> Prop) c, Q c -> sreach Q c.
Proof.
ltac2:(KReplay.run1 (kr_t_BReach ()) ["WithSegs"] "h01Hh11Qh21cp;3p10000p4p70R0p1000`p4p710R1p8P0p1001>p4p7210R2p8P0p1001[p4p710R3p8P0p1002;p4p710R0p8p1002Yp4p70R4P1p8P4P2p8P4P3p8P4P0p8p1003Gp4p7210R4P1p8P4P2p8P4P3p8P4P0p8p10043p4p70R4P1p8P4P2p8P4P3p8P4P0p8g004ij30Tg005dR0p-0[f1R4f0R3O1f2?043W0X20W1o"). Qed.

Lemma sreach_mono : forall (Q Q' : config -> Prop) c,
  sreach Q c -> (forall c', Q c' -> Q' c') -> sreach Q' c.
Proof.
ltac2:(KReplay.run1 (kr_t_BReach ()) ["WithSegs"] "h02c'h11ch23evsh31Hh42HQh54Hallh62Hch72Hkh85Hprogh93Hssh:2IHh;1Qh<2Q'h=1Xp;2p;3p;1p;5p;6g006Yj20Tg004ij39Tg007Tj14Tg0084j13Tg008jj22Tg009Dj18Tg009dj31Tg00:>j25Tg00:Yj56Tg00;Tj67Tg005dR0p-0[R1f2R2f0R3'0f4R4P3O1P4f1R5O1[^00P41043X10f5R6P3O1P2P5P3O29965W6X10p,6sstepcR7P5g00<QR8#4R9%33R:O3X00,20%88R8g00=GR;P7f3R<P5P3O3A1829A1;2:X00,20'5[]=]2P7P4P5P:O3f:/05R;[^00^28P7P6P5P:O3P;[^00^28f8P4P<P2P7f6P5P:O3P<P2P5P3O3W9X00X28D6W:W7W5W8X10P2P5E7W4W3X10X<1W;o"). Qed.

Lemma sreach_seq : forall (Q1 Q2 : config -> Prop) c,
  sreach Q1 c -> (forall c', Q1 c' -> sreach Q2 c') -> sreach Q2 c.
Proof.
ltac2:(KReplay.run1 (kr_t_BReach ()) ["WithSegs"] "h02c'h11ch23evsh31Hh44Hallh52Hch62Hkh75Hprogh83Hssh92IHh:1Kh;2Q1h<2Q2h=1Xp;2p;1p;3p;5p;6g006Yj20Tg007Tj18Tg0084j13Tg008jj21Tg009Dj17Tg009dj32Tg00:>j26Tg00:Yj54Tg00;Tj65Tg005dR0p-0[R1f2R2f0R3'0f4R4P3O1f1R5,04[^00P41043X10f5R6P3O1P2P5P3O2W5X10p,6sstepcR7P5g00<QR8#8R9%33R:O3X00,10%78R8g00=GR;P7f3R<P5P3O3A2829A2;2:X00,10'6[]=]2P7P4P5P:O3f:/05R;[^00^28P7P6P5P:O3P;[^00^28f8P4P<P2P7f6P5P:O3P<P2P5P3O3W8X00X28D4W9W6W4W7X10P2P5E5W:W3X10X<1W;o"). Qed.

Lemma sreach_node : forall c (I : Type) (nx : I -> config) (i0 : I) (Q : config -> Prop),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, sreach Q (nx i)) ->
  sreach Q c.
Proof.
ltac2:(KReplay.run1 (kr_t_BReach ()) ["WithSegs"] "p'0h01ih13Hssh22c'h31Hh41eh53evsh61Xh72sth81Eh95Hcomph:2Hkh;6Hsoundh<1Ih=1Qh>2_Hh?1ci001ch@2i0hA2nxi011si021xp;1p;6p;5p;3p;2p;4p;7p200R0g00>=R1p4p741110p8g007Tj1ATP1j6@Tg00?:j1;Tg0084j10Tg00@3j57Tg009Dj1<Tg009dj31Tg008jR1j23Tg006Yj25Tg00@kj49Tg00:>R2j26Tg00AEj2:Tg00A_j4?Tg002;j78Tg001>j6=Tg00:Yj5>Tf2R3g00=GR4f1R5f0R631'6p=4A1456p=2g005dR7P7\6p-0\7p,4segsR8p,2SCR9f4R:f3R;g00<QR<#AR=V;P3E@P2P8%;9R9f6R>P=P:P6O1#0D7^0:%<<R<P8P9f7R?P5P6D7A1<;=R@P?P6O1#0743X0?,3?[^74]4f5RAPAP6O1,5;]015;?[P6P8P9f8RBP=P>P6O1#0D7^0>P8P9f:R9P5P6D7P9P6O1#094@3X09,39[^74^4<PBP6O1,5>^0BP>P9P7p,6sstepcR8f;RCP=%06RDO3X27PBP?O1P3P?O1C9P8f<REP5P6O3P:P3P5P6O3PEP6O1#0RF94@3X0E,3EP1f=RGA1<:=RHPGP6O1#0RI74;X0G12:DX27,37,6HP6f?RJA1<>=RKPJP6O1#0RL74AP2A1<?=RMf@P5O1#0RN,2>A1<B=12BDX27,37'6P6f9RO=1<=RPP<P=P8fFRQP6P9O3fERRP>O1RS#0RT,2CA1<3=12GDX27,37'6[]1X5<P8PRP=POO3fDPAO1RR#0RU,29P4PTP8fHRVP=P6O3A1<==RW123DX27,37'6]1X64P8fGRXP=PTO3PWPXPBO1#0/2DX27RX,371:<=P7PXPQP?O1RX%0XR=,:4C9C?W1PCP6P5F8W3W1P9P6PBF8W3P5P6O2n2001000000120000000W3W0P5P6O2n2001000000120102000b4W1X64X5<P8PEP5PDO3P:P3%05P6O3%03=4@FX0E,3EP1PG%0;=4HIX0G15C;P6%0A=4KLP2PM%0>/2N15J?P6%0OfCP:O1#0'2P4P7P4P7P6P6PCn0110100021010000X44%09PUP6E=A179RA17CSP7PXP8fIf>PDO315Q5]1X27P8PVPGP=O3PJPBO1W1PEP6PCF8W3P6O1b3W8X>PP5P6O2n2001000000120000000W3X0JP5P6O2n2001000000120102000b4W1X27X5<D>W:W;W9P5P6O2n2001000000121000000W3W=X@5WAX<0W?o"). Qed.

Lemma sreach_silent1 : forall c c' (Q : config -> Prop),
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  sreach Q c' -> sreach Q c.
Proof.
ltac2:(KReplay.run1 (kr_t_BReach ()) ["WithSegs"] "p'0h02Hch12Hnh21Qh31ch42c'h51ii001up;1p;6p;2p;7g007Tj13Tg00>=j62Tg006Yj20Tg00B:j71Tg005dR0p-0\0p,4segsp,2SCf2R1g00C8R2g00<Q#3V2P1V2E2f1R3/01f4R4P2P4V2g00CXP1P3P2f5,04f0P3n01100000100X52F1W0W1W2X40W3o"). Qed.

Lemma sreach_step1 : forall ms model ms' (Q : config -> Prop),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sreach Q (mkCfg ms' model) ->
  sreach Q (mkCfg ms model).
Proof.
ltac2:(KReplay.run1 (kr_t_BReach ()) ["WithSegs"] "h02Hch12Hhh25Hlazyh35Hsteph44Hsvch51Qh65modelh72msh83ms'p;1p;3p;2p;9p;5g00D8j10Tg00D]j1BTg00E;j14Tg00E^j13Tg00F@j1ATg00G7j1;Tg009dj31Tg00GYj25Tg009Dj16Tg00H9j17Tg007Tj18Tg00I1j19Tg00J7j1:Tg00K?j2@Tg00L;j2?Tg00MCj22Tg006Yj2<Tg00N8l9=Tg00O8j5>Tg00P9R0g00Q@g005dp-0[g00R6#0#0#0#0#0#0#B#4R1#3R2f2R3#A%;1R4311511R1#6f3R5#7%8131f5R1#9=124%:0p,4segsR4f6R2'@f4R6,?0311212,<6f8R7f7R8'21228P1P4p,2SCP7P8P2P6P5P3f1M9=f0D>W0W3W4W2W1W5X80W6W7o"). Qed.

Lemma sreach_msteps : forall ms ms' model (Q : config -> Prop),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  sreach Q (mkCfg ms' model) ->
  sreach Q (mkCfg ms model).
Proof.
ltac2:(KReplay.run1 (kr_t_BReach ()) ["WithSegs"] "h02msh12Hch23Hmsh33ms'h42Hhh55Hlazyh65Hsteph74Hsvch82IHh91Qh:5modelh;3ms1h<3ms2p;1p;3p;2p;9p;7g00D8j10Tg00D]j1CTg00E;j1:Tg00E^j15Tg00F@j1BTg00G7j1<Tg009dj33Tg00GYj29Tg009Dj18Tg00H9j16Tg007Tj17Tg00R[j34Tg00MCj22Tg006Yj21Tg00I1j1ATg00J7j1@Tg00K?j2=Tg00L;j2>Tg00SWl9?Tg00TVj7;Tg00P9R0g00Q@g005dp-0[g00R6#0#0#0#0#0#0#C#:R1#5R2f1R3#B%<1R4331911R1#8f2R5#6%7133p,4segsR1f5R6f4R734P1f0R8f6R9'2,16f7R:,25,19[X30X001286,17P8W1X00%A5=324%@0f3R4,=11>0533A4145f9R1f:R5,24'1f;R2,26,15[1272,15P:f<P9P2P5P1P7P4P3P8O1M9?W1W8W2W6W7X<0X;0X00P9P6P8F;W2W5W4W9W:X30W0o"). Qed.

Theorem sreach_realizes : forall (Q : config -> Prop) c T,
  sreach Q c ->
  (forall c', Q c' -> realizes segs c' T) ->
  realizes segs c T.
Proof.
  intros Q c T H K. induction H as [c Hc | c Hprog Hall Hk IH].
  - apply K. exact Hc.
  - destruct Hprog as [c1 Hc1].
    pose (I := {c' : config | sstepc c [] (SNext c')}).
    assert (Hnode : node_ok segs c I (fun _ => []) (fun i => proj1_sig i)).
    { split.
      - intros [c' Hc']. cbn. exact Hc'.
      - intros e st Hss. destruct (Hall e st Hss) as [-> (c' & ->)].
        exists (exist _ c' Hss). split; reflexivity. }
    assert (HT : forall i : I, realizes segs (proj1_sig i) T).
    { intros [c' Hc']. cbn. apply (IH [] c' Hc'). }
    assert (HT0 : T []) by (eapply realizes_nonempty; apply (HT (exist _ c1 Hc1))).
    apply (rz_conseq segs c (t_alt (fun _ : I => t_emit [] T))).
    + apply (rz_node segs c I (fun _ => []) (fun i => proj1_sig i) (fun _ => T) (exist _ c1 Hc1) Hnode HT).
    + intros tr. split.
      * intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
      * intros Htr. exists (exist _ c1 Hc1). exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.

Example sreach_then_exit : forall ms ms1 model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms1 ->
  ms_svc_pending ms1 = Some x8 ->
  is_exit_no x8 ->
  realizes segs (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms1 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_BReach ()) ["WithSegs"] "h02c'h11Hh22Hhh35Hlazyh43Hmsh54Hsvch63Hx8h75modelh82msh93ms1h:2x8p;1p;3p;2p;8p;4p;6p;5g00D8j11Tg00D]j1MTg00E;j1?Tg00E^j1;Tg00F@j1LTg00G7j1BTg009dj32Tg00GYj2>Tg009Dj1=Tg00H9j1<Tg007Tj1:Tg00R[j38Tg00I1j19Tg00UTj2KTg00V6j1JTg00MCj23Tg00W5j25Tg00X3j10Tg00XXj1ATg00Y6j2@Tg00Y\j34Tg00ZAj16Tg00[4j27Tg00AEj2CTg004ij3DTg00\0j8ETg00]0j4FTg00^0j8GTg002;j6HTg00^mj5ITg00P9R0g00Q@g00R6R1#1#1#1#1#1#1#MR2#?R3%;3R4f1R5#L%B3321>33R6#=f2R7#<%:632p,4segsR6f5R8f4R938%98f3R8,K3524%J9g005dR4f0R3f8R:f7R;'3524R<W0R=f6R>,3:g00_oR?,5;%01#0#0#0#0#0#0#A,@2R1542%6>'7P:P;P>P=P9P8P713;>R91C495D=GEP4f9R=/3:P6p,2SCR9P3f:/5?=421%6='7CFX04P6P9P=P:P;P>P8P7GGP5P3EHX1<X04DIW6W5W4W3W2W:W7X90W8o"). Qed.

End WithSegs.

Arguments sreach segs {SC} Q c.
