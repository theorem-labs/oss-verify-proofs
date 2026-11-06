From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09 YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Exec RegisterBridge Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Contract SlotAgree.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Uniform.
Import ListNotations.
Local Open Scope Z_scope.

Section Lift.
Variable B : malloc_syms.
Let segs := ms_segs B.

Lemma cut_free_instr : forall ms model ms',
  m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  cut_free segs (mkCfg ms' model) -> cut_free segs (mkCfg ms model).
Proof using.
  intros ms model ms' Hh Hl Hsvc Hstep Hc tr c' Hstar.
  inversion Hstar as [c0 | c1 evs c2 tr' c3 Hs Hst]; subst.
  - exact (budget_refused_at_no_lazy_instr segs ms model Hl Hsvc).
  - destruct (node_instr segs ms model ms' Hh Hl Hsvc Hstep) as [_ Hall].
    destruct (Hall evs (SNext c2) Hs) as [[] [_ Heq]].
    injection Heq as ->. exact (Hc tr' c' Hst).
Qed.

Lemma cut_free_msteps : forall ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  cut_free segs (mkCfg ms' model) -> cut_free segs (mkCfg ms model).
Proof using.
  intros ms ms' model Hh Hl Hms; induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro Hc; [exact Hc|].
  exact (cut_free_instr ms model ms1 Hh Hl Hsvc Hstep (IH Hc)).
Qed.

Lemma uniform_instr : forall ms model ms',
  m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  uniform segs (mkCfg ms' model) -> uniform segs (mkCfg ms model).
Proof using.
  intros ms model ms' Hh Hl Hsvc Hstep Hu.
  apply (uniform_nonplacement segs _ (fun x8 len => instr_not_placement segs ms model x8 len Hsvc)).
  intros evs c2 Hs.
  destruct (node_instr segs ms model ms' Hh Hl Hsvc Hstep) as [_ Hall].
  destruct (Hall evs (SNext c2) Hs) as [[] [_ Heq]].
  injection Heq as ->. exact Hu.
Qed.

Lemma uniform_msteps : forall ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  uniform segs (mkCfg ms' model) -> uniform segs (mkCfg ms model).
Proof using.
  intros ms ms' model Hh Hl Hms; induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro Hu; [exact Hu|].
  exact (uniform_instr ms model ms1 Hh Hl Hsvc Hstep (IH Hu)).
Qed.

Lemma crealizes_msteps : forall ms ms' model T,
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  crealizes B (mkCfg ms' model) T -> crealizes B (mkCfg ms model) T.
Proof using.
  intros ms ms' model T Hh Hl Hms H. apply crealizes_intro.
  - exact (rz_msteps segs ms ms' model T Hh Hl Hms (crealizes_realizes B _ T H)).
  - exact (cut_free_msteps ms ms' model Hh Hl Hms (crealizes_cut_free B _ T H)).
  - exact (uniform_msteps ms ms' model Hh Hl Hms (crealizes_uniform B _ T H)).
Qed.

Lemma evt_SRcf : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q ms -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', Q ms' -> SRcf B (mkCfg ms' md) P) -> SRcf B (mkCfg ms md) P.
Proof using.
  intros ms Q md P [final [Hs HQ]] Hh Hl K T HK.
  apply (crealizes_msteps ms final md T Hh Hl (lib_msteps_frame segs ms final Hs)).
  exact (K final HQ T HK).
Qed.

Lemma evt_SRcf_canon : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SRcf B (mkCfg ms' md) P) ->
  SRcf B (mkCfg ms md) P.
Proof using.
  intros ms Q md P H Hh Hl K.
  exact (evt_SRcf ms _ md P (RegisterBridge.canonical_contract_transport segs Q ms H) Hh Hl K).
Qed.

Lemma SRcf_ret : forall c (Q : config -> Prop), Q c -> SRcf B c Q.
Proof using. intros c Q HQ T HK. exact (HK c HQ). Qed.

Lemma SRcf_bind : forall c (R Q : config -> Prop),
  SRcf B c R -> (forall c', R c' -> SRcf B c' Q) -> SRcf B c Q.
Proof using. intros c R Q H1 H2 T HK. apply H1. intros c' HR. exact (H2 c' HR T HK). Qed.

Lemma SRcf_mono : forall c (Q Q' : config -> Prop),
  SRcf B c Q -> (forall c', Q c' -> Q' c') -> SRcf B c Q'.
Proof using. intros c Q Q' H HQQ T HK. apply H. intros c' HQ. exact (HK c' (HQQ c' HQ)). Qed.
End Lift.
