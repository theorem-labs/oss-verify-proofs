(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11-05: copied from projects/cgif/cgif_rgb_fuzzer/proofs/lib/HaltsFO.v at c395a1e0dfa,
   lines 13-171 and 314-316, with its lead comment replaced by this line.  The import of that tree's YK15 becomes
   OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.ShapeAlg, which holds the same TSet algebra, the same node_ok over
   plain sstep and the same three-constructor realizes.  Its lines 173-311 (injected_family_off_*, fo_dead_refusal*,
   fo_dead_node, refusal_b_*, ret_in_errnos_*, small_not_errno, mmap_*_refusal, apply_effect_a0) are not copied:
   nothing here needs a dead refusal arm, because the plain and UBSan closures of this target are built with realizes,
   which has no spin constructor. *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.

Definition ev_ok (S : list word) (e : event) : Prop :=
  match e with
  | ExitEv k _ => In k S
  | KillEv _ _ => False
  | _ => True
  end.
Definition trace_ok (S : list word) (tr : list event) : Prop := Forall (ev_ok S) tr.
Definition shape_ok (S : list word) (T : TSet) : Prop := forall tr, T tr -> trace_ok S tr.

Lemma trace_ok_app : forall S a b, trace_ok S (a ++ b) <-> trace_ok S a /\ trace_ok S b.
Proof. intros S a b. unfold trace_ok. apply Forall_app. Qed.
Lemma trace_ok_prefix : forall S tr tr', is_prefix tr tr' -> trace_ok S tr' -> trace_ok S tr.
Proof.
  intros S tr; induction tr as [|e tr IH]; intros tr' Hp Hok.
  - constructor.
  - destruct tr' as [|e' tr']; cbn in Hp; [destruct Hp|]. destruct Hp as [<- Hp].
    inversion Hok; subst. constructor; [assumption|]. eapply IH; eauto.
Qed.
Lemma shape_ok_eq : forall S T T', t_eq T T' -> shape_ok S T' -> shape_ok S T.
Proof. intros S T T' Heq H tr Htr. apply H. apply Heq. exact Htr. Qed.
Lemma shape_ok_eq' : forall S T T', t_eq T T' -> shape_ok S T -> shape_ok S T'.
Proof. intros S T T' Heq H tr Htr. apply H. apply Heq. exact Htr. Qed.
Lemma shape_ok_nil : forall S, shape_ok S t_nil.
Proof. intros S tr Htr. unfold t_nil in Htr. subst tr. constructor. Qed.
Lemma shape_ok_emit : forall S evs T, trace_ok S evs -> shape_ok S T -> shape_ok S (t_emit evs T).
Proof.
  intros S evs T Hevs HT tr [Hp | (tr' & -> & Htr')].
  - eapply trace_ok_prefix; eauto.
  - apply trace_ok_app. split; [exact Hevs | apply HT; exact Htr'].
Qed.
Lemma shape_ok_emit_inv : forall S evs T, T [] -> shape_ok S (t_emit evs T) -> trace_ok S evs /\ shape_ok S T.
Proof.
  intros S evs T H0 H. split.
  - apply (H evs). right. exists []. rewrite app_nil_r. split; [reflexivity | exact H0].
  - intros tr Htr. assert (Hc : trace_ok S (evs ++ tr)).
    { apply H. right. exists tr. split; [reflexivity | exact Htr]. }
    apply trace_ok_app in Hc. tauto.
Qed.
Lemma shape_ok_alt : forall S (I : Type) (f : I -> TSet), (forall i, shape_ok S (f i)) -> shape_ok S (t_alt f).
Proof. intros S I f H tr [i Hi]. exact (H i tr Hi). Qed.
Lemma shape_ok_alt_inv : forall S (I : Type) (f : I -> TSet) i, shape_ok S (t_alt f) -> shape_ok S (f i).
Proof. intros S I f i H tr Htr. apply H. exists i. exact Htr. Qed.
Lemma shape_ok_alt2 : forall S A B, shape_ok S A -> shape_ok S B -> shape_ok S (t_alt2 A B).
Proof. intros S A B HA HB tr [H|H]; [apply HA | apply HB]; exact H. Qed.
Lemma shape_ok_exit : forall S code fs, In code S -> shape_ok S (t_exit code fs).
Proof.
  intros S code fs Hin. unfold t_exit. apply shape_ok_emit; [|apply shape_ok_nil].
  constructor; [exact Hin | constructor].
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition fo_exits (c : config) (T : TSet) : Prop :=
  forall S : list word, shape_ok S T -> m_halted (cfg_model c) = None ->
    must_exit_in_at_cfg forced_only_cfg segs S c.

(* [comment removed for export] *)
Definition fo_dead (c c' : config) : Prop :=
  forall e, ~ sstep_cfg segs forced_only_cfg c e (SNext c').

Lemma fo_conseq : forall c T T', fo_exits c T -> t_eq T T' -> fo_exits c T'.
Proof. intros c T T' H E S HS Hh. exact (H S (shape_ok_eq S T T' E HS) Hh). Qed.

Lemma fo_halted : forall c T, m_halted (cfg_model c) <> None -> fo_exits c T.
Proof. intros c T Hh S _ Hn. exfalso. exact (Hh Hn). Qed.

(* [comment removed for export] *)
Lemma fo_progress : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (i0 : I),
  node_ok segs c I evs nx ->
  exists e st, sstep_cfg segs forced_only_cfg c e st.
Proof.
  intros c I evs nx i0 [Hcomp Hsound].
  pose proof (Hcomp i0) as Hss.
  assert (NOERR : forall e, ~ sstep segs c e SError).
  { intros e He. destruct (Hsound e SError He) as (i & _ & Hbad). discriminate Hbad. }
  remember (evs i0) as e0. remember (SNext (nx i0)) as st0. clear Heqe0 Heqst0.
  destruct Hss.
  - eexists _, _. eapply sstep_cfg_instr; eassumption.
  - eexists _, _. eapply sstep_cfg_instr_fault; eassumption.
  - eexists _, _. eapply sstep_cfg_instr_unmodeled; eassumption.
  - destruct (classic (spurious_refusal_cfg forced_only_cfg (sys_input segs ms x8) model eff)) as [Hsp | Hns].
    + destruct Hsp as (_ & _ & eff' & m' & evs' & Hspec' & Hnr').
      assert (Hns' : ~ spurious_refusal_cfg forced_only_cfg (sys_input segs ms x8) model eff').
      { apply spurious_refusal_not_refusal. exact Hnr'. }
      destruct (m_halted m') as [code|] eqn:Hh'.
      * destruct (m_killed m') as [sig|] eqn:Hk'.
        -- eexists _, _. eapply sstep_cfg_killed; eassumption.
        -- eexists _, _. eapply sstep_cfg_exit; eassumption.
      * destruct (materialize_model_accesses m' (syscall_effect_accesses eff')) as [m''|] eqn:Hmat.
        -- eexists _, _. eapply sstep_cfg_syscall; eassumption.
        -- exfalso. apply (NOERR []). eapply sstep_syscall_materialization_fault; eassumption.
    + eexists _, _. eapply sstep_cfg_syscall; eassumption.
  - exfalso. eapply NOERR. eapply sstep_syscall_materialization_fault; eassumption.
  - eexists _, _. eapply sstep_cfg_exit; eassumption.
  - eexists _, _. eapply sstep_cfg_killed; eassumption.
  - exfalso. eapply NOERR. eapply sstep_syscall_unmodeled; eassumption.
Qed.

(* [comment removed for export] *)
Lemma fo_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I)
    (dead : I -> Prop),
  node_ok segs c I evs nx ->
  (forall i, dead i -> fo_dead c (nx i)) ->
  (forall i, ~ dead i -> fo_exits (nx i) (T i)) ->
  (forall i, ~ dead i -> T i []) ->
  fo_exits c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 dead Hnode Hdead Hlive Hne S HS Hrun.
  destruct Hnode as [Hcomp Hsound].
  apply must_exit_in_at_cfg_running.
  - exact Hrun.
  - exact (fo_progress c I evs nx i0 (conj Hcomp Hsound)).
  - intros e Hss. apply sstep_cfg_sub in Hss. destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate Hbad.
  - intros e c' Hss.
    pose proof (sstep_cfg_sub _ _ _ _ _ Hss) as Hss'.
    destruct (Hsound e (SNext c') Hss') as (i & -> & Heq). injection Heq as Heq. subst c'.
    destruct (classic (dead i)) as [Hd | Hl].
    + exfalso. exact (Hdead i Hd _ Hss).
    + pose proof (shape_ok_alt_inv S I _ i HS) as HSi.
      destruct (shape_ok_emit_inv S (evs i) (T i) (Hne i Hl) HSi) as [Hevs HTi].
      destruct (sstep_next_halts_by_exit segs c (evs i) (nx i) Hss')
        as [Hn | [(evs0 & code & Hevs' & Hh & Hk) | (evs0 & sig & Hevs' & Hk)]].
      * exact (Hlive i Hl S HTi Hn).
      * apply (must_exit_in_at_cfg_halted forced_only_cfg segs S (nx i) code Hh); [|exact Hk].
        rewrite Hevs' in Hevs. apply trace_ok_app in Hevs as [_ Hev]. inversion Hev; subst. exact H1.
      * exfalso. rewrite Hevs' in Hevs. apply trace_ok_app in Hevs as [_ Hev]. inversion Hev; subst. exact H1.
Qed.

(* [comment removed for export] *)
Lemma fo_node_all : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I evs nx ->
  (forall i, fo_exits (nx i) (T i)) ->
  (forall i, T i []) ->
  fo_exits c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 Hnode Hlive Hne.
  apply (fo_node c I evs nx T i0 (fun _ => False) Hnode).
  - intros i f. destruct f.
  - intros i _. apply Hlive.
  - intros i _. apply Hne.
Qed.

(* [comment removed for export] *)
Lemma fo_of_realizes : forall c T, realizes segs c T -> fo_exits c T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - apply (fo_node_all c I evs nx T i0 Hnode IH).
    intros i. eapply realizes_nonempty. exact (Hcont i).
  - apply fo_halted. exact Hh.
  - eapply fo_conseq; [exact IH | exact Heq].
Qed.

(* [comment removed for export] *)
Lemma fo_exits_must_exit : forall S c T,
  fo_exits c T -> shape_ok S T -> m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof. intros S c T H HS Hh. exact (H S HS Hh). Qed.

End WithSegs.

Definition codes02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma in_codes02_0 : In (Z_to_bv 64 0) codes02. Proof. left. reflexivity. Qed.
Lemma in_codes02_2 : In (Z_to_bv 64 2) codes02. Proof. right. left. reflexivity. Qed.
