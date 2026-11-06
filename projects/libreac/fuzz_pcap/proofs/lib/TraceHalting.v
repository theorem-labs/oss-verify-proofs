(** Derive termination from the published inductive trace certificates.
    A trace certificate alone does not restrict exit statuses or exclude kills;
    those obligations are explicit below. Restricting environment failures
    additionally requires LPS's original progress/decision premise. *)
From Stdlib Require Import ZArith List Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit Equivalence.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK15.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.R Require Import Cfg.
Import ListNotations.

Definition permitted_event (allowed : list word) (e : event) : Prop :=
  match e with
  | ExitEv code _ => In code allowed
  | KillEv _ _ => False
  | _ => True
  end.
Definition permitted_traces (allowed : list word) (T : TSet) : Prop :=
  forall tr, T tr -> Forall (permitted_event allowed) tr.
Definition permitted_halt (allowed : list word) (c : config) : Prop :=
  match m_halted (cfg_model c) with
  | None => True
  | Some code => In code allowed /\ m_killed (cfg_model c) = None
  end.

Lemma refusal_decided_classical : forall cfg i model,
  refusal_decided cfg i model.
Proof.
  intros cfg i model Hfamily.
  destruct (classic (exists eff next events,
    syscall_spec i model (Ok eff next events) /\ refusal_b i model (eff_ret eff) = false))
    as [Hsuccess | Hnone].
  - left. exact Hsuccess.
  - right. intros eff next events Hspec.
    destruct (refusal_b i model (eff_ret eff)) eqn:Hrefusal; [reflexivity |].
    exfalso. apply Hnone. exists eff, next, events. auto.
Qed.

Lemma decided_from_classical : forall cfg segs c, decided_from cfg segs c.
Proof.
  intros cfg segs c tr c' x8 Hstar Hpending.
  apply refusal_decided_classical.
Qed.
