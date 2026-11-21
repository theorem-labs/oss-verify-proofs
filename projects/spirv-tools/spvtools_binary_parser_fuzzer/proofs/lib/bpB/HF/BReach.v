(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (each node of a walk asks that its system call answers the same over a larger read-only backing (RomBase.sys_rob), so a walk over the image's own segments lifts to the run's segment list; recorded proofs written as text where the node premise changed their terms). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BSimInv BExitSim BCatSim BShapeAlg.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.Cfg Require RomBase.
Ltac2 kr_t_BReach () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init6Specif9proj1_sigC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufk69OSSVerify5KrLib3bpB2HF6BReach6sreach01C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00i69OSSVerify5KrLib3bpB2HF6BReach6sreach00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00k69OSSVerify5KrLib3bpB2HF6BReach6sreach02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF6BReach:sreach_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00C69OSSVerify5KrLib3bpB2HF9BShapeAlg7node_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF4Bcfg8the_scfgC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01c69OSSVerify5KrLib3bpB2HF6BReach;sreach_nodeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib3bpB2HF9BShapeAlg:node_instrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF6BReach>sreach_silent1C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib3bpB2HF7BCatSim6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF6BReach<sreach_step1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF7BCatSim:msteps_indC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib3bpB2HF8BExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC69OSSVerify5KrLib3bpB2HF9BShapeAlg6t_exitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF6BReach=sreach_mstepsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpB2HF9BShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BShapeAlg7rz_exitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF6BReach?sreach_realizesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01".
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
    RomBase.sys_rob segs c ->   (* LPS 08b1429: as [BShapeAlg.rz_node], for [sreach_realizes] *)
    (exists c', sstepc c [] (SNext c')) ->
    (forall evs X, sstepc c evs X -> evs = [] /\ exists c', X = SNext c') ->
    (forall evs c', sstepc c evs (SNext c') -> sreach Q c') ->
    sreach Q c.

Lemma sreach_done : forall (Q : config -> Prop) c, Q c -> sreach Q c.
Proof. intros Q c H. apply sr_done. exact H. Qed.

Lemma sreach_mono : forall (Q Q' : config -> Prop) c,
  sreach Q c -> (forall c', Q c' -> Q' c') -> sreach Q' c.
Proof.
  (* LPS 08b1429: text in place of the recorded proofs, for [sr_step]'s new premise *)
  intros Q Q' c H HQ. induction H as [c Hc | c Hrob Hprog Hall Hk IH].
  - apply sr_done. apply HQ. exact Hc.
  - apply sr_step; [exact Hrob | exact Hprog | exact Hall |].
    intros evs c' Hss. exact (IH evs c' Hss).
Qed.

Lemma sreach_seq : forall (Q1 Q2 : config -> Prop) c,
  sreach Q1 c -> (forall c', Q1 c' -> sreach Q2 c') -> sreach Q2 c.
Proof.
  intros Q1 Q2 c H K. induction H as [c Hc | c Hrob Hprog Hall Hk IH].
  - apply K. exact Hc.
  - apply sr_step; [exact Hrob | exact Hprog | exact Hall |].
    intros evs c' Hss. exact (IH evs c' Hss).
Qed.

Lemma sreach_node : forall c (I : Type) (nx : I -> config) (i0 : I) (Q : config -> Prop),
  node_ok segs c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, sreach Q (nx i)) ->
  sreach Q c.
Proof.
  intros c I nx i0 Q [Hcomp Hsound] Hrob Hk.
  apply sr_step; [exact Hrob | | |].
  - exists (nx i0). apply (Hcomp i0).
  - intros evs X Hss. destruct (Hsound evs X Hss) as (i & -> & ->).
    split; [reflexivity|]. exists (nx i). reflexivity.
  - intros evs c' Hss. destruct (Hsound evs (SNext c') Hss) as (i & _ & E).
    injection E as ->. apply Hk.
Qed.

Lemma sreach_silent1 : forall c c' (Q : config -> Prop),
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  sreach Q c' -> sreach Q c.
Proof. intros c c' Q Hn Hrob Hc. apply (sreach_node c unit (fun _ => c') tt Q Hn Hrob). intros []; exact Hc. Qed.

Lemma sreach_step1 : forall ms model ms' (Q : config -> Prop),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sreach Q (mkCfg ms' model) ->
  sreach Q (mkCfg ms model).
Proof.
  intros ms model ms' Q Hh Hlazy Hsvc Hstep Hc.
  eapply sreach_silent1; [apply node_instr; eassumption | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

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
  intros Q c T H K. induction H as [c Hc | c Hrob Hprog Hall Hk IH].
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
    + apply (rz_node segs c I (fun _ => []) (fun i => proj1_sig i) (fun _ => T) (exist _ c1 Hc1) Hnode Hrob HT).
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
