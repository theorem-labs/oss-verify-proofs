(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BLPropExec BMState BMem BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Export Bcfg.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BITree () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appc7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree9itree_indc7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree4impli7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree5itree00k7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree5itree01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec8evt_monok7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree5itree02c7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree4nretI47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree4respC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec3evtC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec7evt_cutc7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITreeBleaves_unreachablec7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITreeDleaves_unreachable_mc7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree5tpathc7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree7tree_atc7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree5tsafec7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree7run_invc7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree5ebindc7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree4bindc7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree9impl_monoc7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree5eposti8ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree3Exc3exc00k8ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree3Exc3exc01k8ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BITree3Exc3exc02I47Corelib4Init5Logic4True00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition resp := SyscallEffect.
Definition nret (ms : machine_state) (eff : resp) : machine_state :=
  advance_past_svc (apply_effect ms eff).

Module Exc.
#[universes(template)]
Inductive exc (A : Type) : Type := Unr | Ok (a : A).
Arguments Unr {A}.
Arguments Ok {A} a.
End Exc.
Import Exc.

Section ITree.

Variable node : Type.

Inductive itree (R : Type) : Type :=
| Ret (r : R)
| Vis (n : node) (k : resp -> itree R).
Arguments Ret {R} r.
Arguments Vis {R} n k.

Fixpoint bind {A B} (t : itree A) (f : A -> itree B) : itree B :=
  match t with
  | Ret r => f r
  | Vis n k => Vis n (fun x => bind (k x) f)
  end.

Variable segs : list Segment.

Context {SC : StepCfg}.
#[local] Notation SSTEP := (sstep_cfg segs the_scfg).
#[local] Notation STAR := (star_cfg segs the_scfg).

Variable at_node : node -> machine_state -> Prop.

Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.

Variable nsafe : node -> Model -> Prop.

Variable minv_lazy : forall mo, minv mo -> m_vm_lazy mo = [].

Record node_sound : Prop := {

  ns_pending : forall n ms, at_node n ms -> ms_svc_pending ms <> None;

  ns_complete : forall n ms mo evs X, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      SSTEP (mkCfg ms mo) evs X ->
        (exists rsp mo', X = SNext (mkCfg (nret ms rsp) mo') /\ nstep n mo rsp mo' evs)
     \/ (exists code mo', X = SNext (mkCfg ms mo') /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')]);

  ns_sound : forall n ms mo rsp mo' evs, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nstep n mo rsp mo' evs ->
      m_halted mo' = None /\ minv mo'
      /\ SSTEP (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo'));
  ns_exit : forall n ms mo code mo', at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nexit n mo code mo' ->
      m_halted mo' = Some code /\ SSTEP (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo'));

  ns_progress : forall n ms mo, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      (exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo')
}.

Fixpoint impl {R} (t : itree R) (Q : R -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match t with
  | Ret r => evt segs (Q r) ms
  | Vis n k => evt segs (fun ms1 => at_node n ms1 /\ forall rsp, impl (k rsp) Q (nret ms1 rsp)) ms
  end.

Lemma impl_mono : forall {R} (t : itree R) (Q Q' : R -> machine_state -> Prop) ms,
  impl t Q ms -> (forall r ms', Q r ms' -> Q' r ms') -> impl t Q' ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BITree ()) ["ITree"] "h03rsph11Qh22Q'h32msh43ms1h51rh61Hh72H0h82HQh93ms'h:1th;3Hath<2Hkh=2IHh>1Rh?1kh@1np;1p;4p;2p;6p;3p;5p10000p4p70p1000^p4p710p8p200R0g001;R1p60721001p8P0g002;R2p6074111002p8g0036j13TP2j40Tg0044j25Tg0052j64Tg0060j36Tg006nj21Tg007iR2j22Tg008Dj48TP1j57Tf0R1#3f1R3%33f2R4g008_R5p-0[R6[R7f3R8P6[R9f5R:P8P4P1C0f6R;P:P3P1O2P:P4P3O2[^95R<]5R=f7R>P:P8P4C0[[^35]2]1W:P:15:8P4P1C0p,4segsR?f4R@P:O1P8P:O1P4P3P:P;P1O2P4P>P3P1O3W7X95E4P>15>:P8P4C0eX8=W6X35X29X17X53p,4nodeg009fR7%38[P6\@R9P6\:R6P>P@P8O1P4P1C0f8R=P<]5R<f9RAP;P:O1P8P4C0[[^35]2]1\7P>A6>:@P4P1C0P?p,7at_nodeR?P=P1O2R@f;RBP=P1O1R=P;1131RCC0^07'2X45PBP=P:PCC0^07,2@X45P4P3P?PAP1O2f<R@PAP1O1R=P>PCC0^07'2X45P1O1P2P?PAP3O2P@P=P>1141C0^07P?f:R=P4O2f=R2P=P1O1P>1181C0^07'2P1P?PBP8O2f?P@P1O1P=11:1C0^07P?P2P:O2f@P2P1O1P=11;1R2C0^07P3P@P1PBP=P2P3P1O1P>O6X07C8W<W;P3P1O2n2001000000120000000W7X45E4PAA6A>;P8P4C0eX8<W6X35X26X19W=W?W@P1D7W:X>0o"). Qed.

Lemma impl_evt : forall {R} (t : itree R) Q P ms,
  evt segs P ms -> (forall ms', P ms' -> impl t Q ms') -> impl t Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BITree ()) ["ITree"] "p'0h01Kh13ms'h21Hh31Ph41Qh51Rh61ki001kh72msh83ms1h91ni011nh:1ri021rh;3rsph<1ti031ip;1p;3p;4p;2p;6p200R0g002;R1p6074111002p8g0036R2j12Tg00:aj37TP1j40Tg0044j21Tg00;Zj64Tg0060j33Tg006nj26Tg007ij25Tf0R1#2f1R3g008_R4p-0[R5[p,4segsR6?731f3R7P1O1R8f7R9f6R:f5R;P3C0[^14P2P:P;P1O1f9R2f2R<P9P3C0[^14f8R=P3P:f4R>C0]0P;P:P1O1f:R?11?<P=P3C0[^14P6P:P9P3O1P;P>P1E4P21123P9P;C0eW0X:9P1O1p,4nodeg009fR;%2?[P=P1O1f<R>A3>7<P?P3C0[^14P6P=p,7at_nodeP7P1O2f=P8f;R81631C0^;;'5X84P9P:P1E4P8A38<3P2P9C0eW0W6W9P3P1O2n10110300021010220101100P1O1W0W2X74X35W4W<X50o"). Qed.

Fixpoint ttrace {R} (t : itree R) (mo : Model) (tr : list event) : Prop :=
  match t with
  | Ret _ => tr = []
  | Vis n k => (exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')])
            \/ (exists rsp mo' evs tr', nstep n mo rsp mo' evs /\ ttrace (k rsp) mo' tr' /\ tr = evs ++ tr')
  end.

Fixpoint tsafe {R} (t : itree R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> tsafe (k rsp) mo'
  end.

Fixpoint tpath {R} (t : itree R) (mo : Model) (tr : list event) (r : R) (mo' : Model) : Prop :=
  match t with
  | Ret r0 => r0 = r /\ mo' = mo /\ tr = []
  | Vis n k => exists rsp mo1 evs tr', nstep n mo rsp mo1 evs /\ tpath (k rsp) mo1 tr' r mo' /\ tr = evs ++ tr'
  end.

Fixpoint texit {R} (t : itree R) (mo : Model) (tr : list event) : Prop :=
  match t with
  | Ret _ => False
  | Vis n k => (exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')])
            \/ (exists rsp mo' evs tr', nstep n mo rsp mo' evs /\ texit (k rsp) mo' tr' /\ tr = evs ++ tr')
  end.

Definition leaves_unreachable {R} (t : itree R) (ms : machine_state) : Prop :=
  impl t (fun _ _ => False) ms.

Definition leaves_unreachable_m {R} (t : itree R) (mo : Model) : Prop :=
  forall tr r mo', tpath t mo tr r mo' -> False.

Definition tree_at {R} (t : itree R) Q (ms : machine_state) (mo : Model) : Prop :=
  impl t Q ms /\ leaves_unreachable_m t mo /\ m_halted mo = None /\ minv mo /\ tsafe t mo.

Definition run_inv {R} Q (c : config) : Prop :=
  (exists t : itree R, tree_at t Q (cfg_ms c) (cfg_model c))
  \/ m_halted (cfg_model c) <> None.

Definition ebind {A B} (t : itree (exc A)) (f : A -> itree (exc B)) : itree (exc B) :=
  bind t (fun r => match r with Unr => Ret Unr | Ok a => f a end).

Definition epost {A} (Q : A -> machine_state -> Prop) : exc A -> machine_state -> Prop :=
  fun r ms => match r with Unr => True | Ok a => Q a ms end.

Lemma impl_epost_mono : forall {A} (t : itree (exc A)) (Q Q' : A -> machine_state -> Prop) ms,
  impl t (epost Q) ms -> (forall a ms', Q a ms' -> Q' a ms') -> impl t (epost Q') ms.
Proof.
ltac2:(KReplay.run1 (kr_t_BITree ()) ["ITree"] "p'0h03ms'h12H0h21ai001ah31Ah41Hh52HQh61Qh72Q'h82msh91rh:1ti011ep;1p;2p;4p;7p100<Wp6074111001g002;R0p6074111002R1p8p100=`p607311001R2p100>kp607311001p8p100?gp6077111111002R3P1p8P3p100@ep6074111001p8P3P2p8p100Aap6077111111002P3p8p100B_R3p60721001p100C[R2p60721001p8P3p607311000P2p607311000p8p200R2P1p8P2g00DVR1p6074111002p8P2g00EVR3p6071002p8g00FRR4j12Tg0036j17TP3j21j40TP0j45Tg00GRj14Tg00HRj23TP1j76Tf0R1#2#7f1R0g008_R3p-0[R5[f2R6P5[f4R5#2f3R71156P1C5f5R8P8P0P1O2P8P6P0O2[^03]2f6R9#2R:P811951197P6P0P4f7R4f9R7P4P0P1C0f:R5P4P6P0C0[^03P1g00IRP1W1f8R4P9%44P1C0P7P9%47P0C0[eX03P4P0P1O2P8P6P0P1O3W1P5P41350P1C0f;R5P41356P0C0[eX03X24P1O1n10110100020010100X9:F6W5W4X83W7W6W:X32o"). Qed.

Definition enode {A} (n : node) (pl : resp -> option A) : itree (exc A) :=
  Vis n (fun rsp => match pl rsp with Some a => Ret (Ok a) | None => Ret Unr end).

End ITree.

Arguments Ret {node R} r.
Arguments Vis {node R} n k.
Arguments impl {node} segs at_node {R} t Q ms.
Arguments ttrace {node} nstep nexit {R} t mo tr.
Arguments tsafe {node} nstep nsafe {R} t mo.
Arguments tpath {node} nstep {R} t mo tr r mo'.
Arguments texit {node} nstep nexit {R} t mo tr.
Arguments leaves_unreachable_m {node} nstep {R} t mo.
Arguments tree_at {node} segs at_node nstep minv nsafe {R} t Q ms mo.
Arguments ebind {node A B} t f.
Arguments enode {node A} n pl.
