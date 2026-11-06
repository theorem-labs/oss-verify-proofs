(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Unset Lia Cache.

Section WithSegs.
Variable segs : list Segment.

Inductive asteps : machine_state -> Model -> machine_state -> Model -> Prop :=
| ast_refl : forall ms mo, asteps ms mo ms mo
| ast_step : forall ms mo ms1 mo1 ms2 mo2,
    ms_svc_pending ms = None ->
    mi_account_step segs ms mo = MachineOk (ms1, mo1) ->
    asteps ms1 mo1 ms2 mo2 ->
    asteps ms mo ms2 mo2.

Lemma asteps_one : forall ms mo ms1 mo1,
  ms_svc_pending ms = None -> mi_account_step segs ms mo = MachineOk (ms1, mo1) -> asteps ms mo ms1 mo1.
Proof. intros. eapply ast_step; eauto. apply ast_refl. Qed.

Lemma asteps_trans : forall a ma b mb c mc, asteps a ma b mb -> asteps b mb c mc -> asteps a ma c mc.
Proof. intros a ma b mb c mc H; induction H; intros; [assumption|]. eapply ast_step; eauto. Qed.

Lemma asteps_of_msteps : forall ms ms' mo, m_vm_lazy mo = [] -> msteps segs ms ms' -> asteps ms mo ms' mo.
Proof.
  intros ms ms' mo Hl H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; [apply ast_refl|].
  eapply ast_step; [exact Hsvc| | exact IH].
  rewrite (mi_account_step_no_lazy segs ms mo Hl), Hstep. reflexivity.
Qed.

Lemma sstep_ainstr_inv : forall ms model ms' model' evs st,
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\ st = SNext (mkCfg ms' model').
Proof.
  intros ms model ms' model' evs st Hsvc Hstep Hss.
  inversion Hss; subst; try congruence.
  match goal with H : mi_account_step segs ms model = MachineOk _ |- _ => rewrite Hstep in H; inversion H; subst end.
  split; reflexivity.
Qed.

Lemma node_ainstr : forall ms model ms' model',
  m_halted model = None -> ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model').
Proof.
  intros ms model ms' model' Hh Hsvc Hstep.
  apply two_sided_lift; [apply step_nonspur_instr; exact Hsvc |]. split.
  - intros []. apply (sstep_instr segs ms model ms' model'); assumption.
  - intros e st Hss. destruct (sstep_ainstr_inv ms model ms' model' e st Hsvc Hstep Hss) as [-> ->].
    exists tt. split; reflexivity.
Qed.

Lemma rz_astep : forall ms model ms' model' T,
  m_halted model = None -> ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  realizes segs (mkCfg ms' model') T -> realizes segs (mkCfg ms model) T.
Proof.
  intros ms model ms' model' T Hh Hsvc Hstep Hc.
  eapply rz_silent1; [apply node_ainstr; eassumption | exact Hc].
Qed.

Lemma account_step_halted : forall ms model ms' model',
  mi_account_step segs ms model = MachineOk (ms', model') -> m_halted model' = m_halted model.
Proof.
  intros ms model ms' model' H. unfold mi_account_step in H.
  destruct (step_accesses segs ms) as [report| |]; try discriminate.
  destruct (materialize_model_accesses model (@accessed_ranges _ report)) as [mo|] eqn:M; [|discriminate].
  injection H as _ <-. unfold materialize_model_accesses in M.
  destruct (materialize_accesses _ _ _ _ _); [|discriminate]. injection M as <-. destruct model as [fd [maps lz mat] io fs proc lim]. reflexivity.
Qed.

Lemma rz_asteps : forall ms model ms' model' T,
  m_halted model = None -> asteps ms model ms' model' ->
  realizes segs (mkCfg ms' model') T -> realizes segs (mkCfg ms model) T.
Proof.
  intros ms model ms' model' T Hh H. revert Hh.
  induction H as [ms mo | ms mo ms1 mo1 ms2 mo2 Hsvc Hstep Hms IH]; intros Hh Hc; [exact Hc|].
  eapply rz_astep; [exact Hh | exact Hsvc | exact Hstep |].
  apply IH; [|exact Hc]. rewrite (account_step_halted _ _ _ _ Hstep). exact Hh.
Qed.

End WithSegs.
