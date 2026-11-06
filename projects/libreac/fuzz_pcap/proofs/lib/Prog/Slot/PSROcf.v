From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09 YO0d YO05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Exec RegisterBridge Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Contract OutForm SlotAgree AgreeLift.
Import ListNotations.
Local Open Scope Z_scope.

(* The output form of the cut-free contracts: the run from c writes out to fd 2, reaches a state of Q, and no
   configuration it can reach is refused by the memory budget (cut_free). SROcf is to SRO (OutForm.v) what SRcf is
   to SR (SlotAgree.v). *)
Section O.
Variable segs : list Segment.

Definition SROcf (c : config) (out : list byte) (Q : config -> Prop) : Prop :=
  forall T, (forall c', Q c' -> realizes segs c' T /\ cut_free segs c') ->
    realizes segs c (wr ch_stderr out T) /\ cut_free segs c.

Lemma SROcf_bind : forall c o1 o2 (R Q : config -> Prop),
  SROcf c o1 R -> (forall c', R c' -> SROcf c' o2 Q) -> SROcf c (o1 ++ o2) Q.
Proof.
  intros c o1 o2 R Q H1 H2 T HK.
  destruct (H1 (wr ch_stderr o2 T) (fun c' HR => H2 c' HR T HK)) as [Hr Hc].
  split; [exact (rz_conseq segs c _ _ Hr (wr_app ch_stderr o1 o2 T)) | exact Hc].
Qed.

Lemma SROcf_mono : forall c out (Q Q' : config -> Prop),
  SROcf c out Q -> (forall c', Q c' -> Q' c') -> SROcf c out Q'.
Proof. intros c out Q Q' H HQ T HK. apply H. intros c' Hq. exact (HK c' (HQ c' Hq)). Qed.

Lemma SROcf_ret : forall c (Q : config -> Prop), Q c -> SROcf c [] Q.
Proof.
  intros c Q HQ T HK. destruct (HK c HQ) as [Hr Hc].
  split; [exact (realizes_emit_nil segs c T Hr) | exact Hc].
Qed.

Lemma SROcf_case : forall (A : Prop) c out (Q : config -> Prop),
  (A \/ ~ A) -> (A -> SROcf c out Q) -> (~ A -> SROcf c out Q) -> SROcf c out Q.
Proof. intros A c out Q [a | na] H1 H2; auto. Qed.

Lemma SROcf_eq : forall c o o' (Q : config -> Prop), o = o' -> SROcf c o Q -> SROcf c o' Q.
Proof. intros c o o' Q -> H. exact H. Qed.

End O.

Section B.
Variable B : malloc_syms.
Let segs := ms_segs B.

Lemma SROcf_crealizes : forall c out (Q : config -> Prop) T,
  SROcf segs c out Q -> (forall c', Q c' -> crealizes B c' T) -> crealizes B c (wr ch_stderr out T).
Proof. intros c out Q T H HK. exact (H T HK). Qed.

Lemma SRcf_SROcf_bind : forall c out (R Q : config -> Prop),
  SRcf B c R -> (forall c', R c' -> SROcf segs c' out Q) -> SROcf segs c out Q.
Proof. intros c out R Q H1 H2 T HK. apply (H1 (wr ch_stderr out T)). intros c' HR. exact (H2 c' HR T HK). Qed.

Lemma SROcf_SRcf_bind : forall c out (R Q : config -> Prop),
  SROcf segs c out R -> (forall c', R c' -> SRcf B c' Q) -> SROcf segs c out Q.
Proof. intros c out R Q H1 H2 T HK. apply H1. intros c' HR. exact (H2 c' HR T HK). Qed.

Lemma SRcf_to_SROcf : forall c (Q : config -> Prop), SRcf B c Q -> SROcf segs c [] Q.
Proof.
  intros c Q H T HK. destruct (H T HK) as [Hr Hc].
  split; [exact (realizes_emit_nil segs c T Hr) | exact Hc].
Qed.

Lemma SROcf_msteps : forall ms ms' md out (Q : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> msteps segs ms ms' ->
  SROcf segs (mkCfg ms' md) out Q -> SROcf segs (mkCfg ms md) out Q.
Proof.
  intros ms ms' md out Q Hh Hl Hms H T HK.
  exact (crealizes_msteps B ms ms' md _ Hh Hl Hms (H T HK)).
Qed.

Lemma evt_SROcf : forall ms (Q : machine_state -> Prop) md out (P : config -> Prop),
  Exec.evt segs Q ms -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', Q ms' -> SROcf segs (mkCfg ms' md) out P) -> SROcf segs (mkCfg ms md) out P.
Proof.
  intros ms Q md out P [final [Hs HQ]] Hh Hl K T HK.
  exact (crealizes_msteps B ms final md _ Hh Hl (lib_msteps_frame segs ms final Hs) (K final HQ T HK)).
Qed.

Lemma evt_SROcf_canon : forall ms (Q : machine_state -> Prop) md out (P : config -> Prop),
  Exec.evt segs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SROcf segs (mkCfg ms' md) out P) ->
  SROcf segs (mkCfg ms md) out P.
Proof.
  intros ms Q md out P H Hh Hl K.
  exact (evt_SROcf ms _ md out P (RegisterBridge.canonical_contract_transport segs Q ms H) Hh Hl K).
Qed.

End B.
