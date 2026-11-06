(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import CatSim.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg. (* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanAcct SpinAlg.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsanAcctShape () := "C69OSSVerify5KrLib2K52AS8AsanAcct7node_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg7node_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K52AS8AsanAcctBrz_step_restrictedC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcctErz_msteps_restricted'C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Lemma node_ok_same : AsanAcct.node_ok segs = ShapeAlg.node_ok segs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctShape ()) ["WithSegs"] "h01Ih11ch23evsh32nxp;1p;2g0000p4p73110R0g000kR1p4p73110R2p8P2P0p8g001fj12TP1j11Tg002Fj20Tg002`R1f0g003U#2[f1P1[p-0]3]2^00]1p,4segs#1'0o"). Qed.

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs c T.

Let P_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    P_of T c' -> P_of T c :=
  fun c c' Hn Hr => rz_silent1 segs c c' T Hn Hr.

Theorem rz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  realizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs (mkCfg ms model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctShape ()) ["WithSegs"] "h01Ah11Th25modelh32msh44msr'p;2p;1p;:g004Kj22Tg001fj11Tg004kl:0Tg0061R0/20#1g006OR0g007Vg008Lp,4segsp,1Hp,2HHp,3Hwxp,4P_off0R1O1p,<P_of_silent1P1O1f4f3f2f1M:0W1W2X40W3W0o"). Qed.

Theorem rz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      realizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs (mkCfg ms model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctShape ()) ["WithSegs"] "h01Ah11Th25modelh32msh44msr'p;2p;1p;:g004Kj22Tg001fj11Tg009Dl:0Tg0061R0/20#1g006OR0g007Vg008Lp,4segsp,1Hp,2HHp,3Hwxp,4P_off0R1O1p,<P_of_silent1P1O1f4f3f2f1M:0W1W2X40W3W0o"). Qed.
(* [comment removed for export] *)
Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs c T.

Let SP_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    SP_of T c' -> SP_of T c :=
  fun c c' Hn Hr => srz_silent1 segs c c' T Hn Hr.

Theorem srz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  srealizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctShape ()) ["WithSegs"] "h01Ah11Th25modelh32msh44msr'p;2p;1p;:g004Kj22Tg001fj11Tg004kl:0Tg0061R0/20#1g006OR0g007Vg008Lp,4segsp,1Hp,2HHp,3Hwxp,5SP_off0R1O1p,=SP_of_silent1P1O1f4f3f2f1M:0W1W2X40W3W0o"). Qed.

Theorem srz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      srealizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctShape ()) ["WithSegs"] "h01Ah11Th25modelh32msh44msr'p;2p;1p;:g004Kj22Tg001fj11Tg009Dl:0Tg0061R0/20#1g006OR0g007Vg008Lp,4segsp,1Hp,2HHp,3Hwxp,5SP_off0R1O1p,=SP_of_silent1P1O1f4f3f2f1M:0W1W2X40W3W0o"). Qed.
End WithSegs.
