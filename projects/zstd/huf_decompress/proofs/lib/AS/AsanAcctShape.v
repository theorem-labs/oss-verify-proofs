(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (rz_step_restricted_T, rz_msteps_restricted_T, srz_step_restricted_T and 1 more); P_of_silent1 and SP_of_silent1 take the premise that no system call is pending and give rz_silent1 and srz_silent1 RomBase.sys_rob through sys_rob_instr; imports RomBase). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import CatSim.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import ShapeAlg. (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanAcct SpinAlg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import RomBase.
Ltac2 kr_t_AsanAcctShape () := "C59OSSVerify5KrLib2AS8AsanAcct7node_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg7node_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib2AS8AsanAcctBrz_step_restrictedC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanAcctErz_msteps_restricted'C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Lemma node_ok_same : AsanAcct.node_ok segs = ShapeAlg.node_ok segs.
Proof. reflexivity. Qed.

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs c T.

Let P_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    ms_svc_pending (cfg_ms c) = None ->
    P_of T c' -> P_of T c :=
  fun c c' Hn Hs Hr => rz_silent1 segs c c' T Hn (sys_rob_instr segs c Hs) Hr.

Theorem rz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  realizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.

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
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.
(* [comment removed for export] *)
Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs c T.

Let SP_of_silent1 (T : TSet) : forall c c',
    AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    ms_svc_pending (cfg_ms c) = None ->
    SP_of T c' -> SP_of T c :=
  fun c c' Hn Hs Hr => srz_silent1 segs c c' T Hn (sys_rob_instr segs c Hs) Hr.

Theorem srz_step_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  srealizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_step_restricted segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.

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
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.
End WithSegs.
