(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import PropExec MState Mem Exec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition resp := SyscallEffect.
Definition nret (ms : machine_state) (eff : resp) : machine_state :=
  advance_past_svc (apply_effect ms eff).

End AC_1.

Module Exc.
#[universes(template)]
Inductive exc (A : Type) : Type := Unr | Ok (a : A).
Arguments Unr {A}.
Arguments Ok {A} a.
End Exc.
Import Exc.
Section AC_2. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

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

Variable at_node : node -> machine_state -> Prop.

Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.

Variable nsafe : node -> Model -> Prop.

Record node_sound : Prop := {

  ns_pending : forall n ms, at_node n ms -> ms_svc_pending ms <> None;

  ns_complete : forall n ms mo evs X, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      sstep segs (mkCfg ms mo) evs X ->
        (exists rsp mo', X = SNext (mkCfg (nret ms rsp) mo') /\ nstep n mo rsp mo' evs)
     \/ (exists code mo', X = SNext (mkCfg ms mo') /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')]);

  ns_sound : forall n ms mo rsp mo' evs, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nstep n mo rsp mo' evs ->
      m_halted mo' = None /\ minv mo'
      /\ sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo'));
  ns_exit : forall n ms mo code mo', at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nexit n mo code mo' ->
      m_halted mo' = Some code /\ sstep segs (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo'));

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
  induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_mono; eauto.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. eapply IH; eauto.
Qed.

Lemma impl_evt : forall {R} (t : itree R) Q P ms,
  evt segs P ms -> (forall ms', P ms' -> impl t Q ms') -> impl t Q ms.
Proof.
  intros R t Q P ms H K. destruct t; cbn in *; eapply evt_cut; eauto; intros ms' HP; apply (K _ HP).
Qed.

Lemma impl_bind : forall {A B} (t : itree A) (f : A -> itree B) Q1 Q ms,
  impl t Q1 ms -> (forall r ms', Q1 r ms' -> impl (f r) Q ms') -> impl (bind t f) Q ms.
Proof.
  induction t as [r|n k IH]; intros f Q1 Q ms H Hf; cbn [bind].
  - cbn in H. eapply impl_evt; [exact H|]. intros ms' HQ. exact (Hf _ _ HQ).
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

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

Lemma tpath_bind : forall {A B} (t : itree A) (f : A -> itree B) mo tr rb mo',
  tpath (bind t f) mo tr rb mo' <->
  exists tr1 r mo1 tr2, tpath t mo tr1 r mo1 /\ tpath (f r) mo1 tr2 rb mo' /\ tr = tr1 ++ tr2.
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo tr rb mo'; cbn.
  - split.
    + intros H. exists [], r, mo, tr. repeat split; auto.
    + intros (tr1 & r0 & mo1 & tr2 & (-> & -> & ->) & H & ->). exact H.
  - split.
    + intros (rsp & mo1 & evs & tr' & Hst & Hp & ->).
      destruct (proj1 (IH rsp f mo1 tr' rb mo') Hp) as (tr1 & r & mo2 & tr2 & H1 & H2 & ->).
      exists (evs ++ tr1), r, mo2, tr2. split; [idtac|split; [exact H2|apply app_assoc]].
      exists rsp, mo1, evs, tr1. repeat split; assumption.
    + intros (tr1 & r & mo2 & tr2 & (rsp & mo1 & evs & tr' & Hst & H1 & ->) & H2 & ->).
      exists rsp, mo1, evs, (tr' ++ tr2). split; [assumption|split; [idtac|symmetry; apply app_assoc]].
      apply (proj2 (IH rsp f mo1 _ rb mo')). exists tr', r, mo2, tr2. repeat split; assumption.
Qed.

Definition leaves_unreachable {R} (t : itree R) (ms : machine_state) : Prop :=
  impl t (fun _ _ => False) ms.

Definition leaves_unreachable_m {R} (t : itree R) (mo : Model) : Prop :=
  forall tr r mo', tpath t mo tr r mo' -> False.

Definition ebind {A B} (t : itree (exc A)) (f : A -> itree (exc B)) : itree (exc B) :=
  bind t (fun r => match r with Unr => Ret Unr | Ok a => f a end).

Definition epost {A} (Q : A -> machine_state -> Prop) : exc A -> machine_state -> Prop :=
  fun r ms => match r with Unr => True | Ok a => Q a ms end.

Lemma impl_ret_unr : forall {A} (Q : A -> machine_state -> Prop) ms, impl (Ret Unr) (epost Q) ms.
Proof. intros A Q ms. cbn. apply evt_done. exact I. Qed.

Lemma impl_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) Q1 Q ms,
  impl t (epost Q1) ms -> (forall a ms', Q1 a ms' -> impl (f a) (epost Q) ms') ->
  impl (ebind t f) (epost Q) ms.
Proof.
  intros A B t f Q1 Q ms Ht Hf. unfold ebind. eapply impl_bind; [exact Ht|].
  intros [|a] ms' H'; cbn in H'.
  - apply impl_ret_unr.
  - apply Hf. exact H'.
Qed.

Lemma impl_epost_mono : forall {A} (t : itree (exc A)) (Q Q' : A -> machine_state -> Prop) ms,
  impl t (epost Q) ms -> (forall a ms', Q a ms' -> Q' a ms') -> impl t (epost Q') ms.
Proof.
  intros A t Q Q' ms H HQ. eapply impl_mono; [exact H|]. intros [|a] ms'; cbn; auto.
Qed.

Lemma ebind_ret_ok : forall {A B} (a : A) (f : A -> itree (exc B)), ebind (Ret (Ok a)) f = f a.
Proof. reflexivity. Qed.

Lemma impl_ret_ok : forall {A} (Q : A -> machine_state -> Prop) a ms,
  evt segs (Q a) ms -> impl (Ret (Ok a)) (epost Q) ms.
Proof. intros A Q a ms H. exact H. Qed.

Definition enode {A} (n : node) (pl : resp -> option A) : itree (exc A) :=
  Vis n (fun rsp => match pl rsp with Some a => Ret (Ok a) | None => Ret Unr end).

Lemma impl_enode : forall {A} n (pl : resp -> option A) (Q : A -> machine_state -> Prop) ms,
  evt segs (fun ms1 => at_node n ms1 /\ forall rsp a, pl rsp = Some a -> evt segs (Q a) (nret ms1 rsp)) ms ->
  impl (enode n pl) (epost Q) ms.
Proof.
  intros A n pl Q ms H. cbn. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn.
  - apply Hk. reflexivity.
  - apply evt_done. exact I.
Qed.

Lemma tpath_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo tr r mo',
  tpath (ebind t f) mo tr r mo' <->
  (tpath t mo tr Unr mo' /\ r = Unr)
  \/ exists tr1 a mo1 tr2, tpath t mo tr1 (Ok a) mo1 /\ tpath (f a) mo1 tr2 r mo' /\ tr = tr1 ++ tr2.
Proof.
  intros A B t f mo tr r mo'. unfold ebind. rewrite tpath_bind. split.
  - intros (tr1 & [|a] & mo1 & tr2 & H1 & H2 & ->).
    + cbn in H2. destruct H2 as (<- & -> & ->). left. rewrite app_nil_r. split; [exact H1|reflexivity].
    + right. exists tr1, a, mo1, tr2. repeat split; assumption.
  - intros [[H1 ->]|(tr1 & a & mo1 & tr2 & H1 & H2 & ->)].
    + exists tr, Unr, mo', []. split; [exact H1|]. split; [cbn; repeat split; reflexivity| symmetry; apply app_nil_r].
    + exists tr1, (Ok a), mo1, tr2. repeat split; assumption.
Qed.

End ITree.
End AC_2.

Arguments Ret {node R} r.
Arguments Vis {node R} n k.
Arguments impl {node} segs at_node {R} t Q ms.
Arguments ttrace {node} nstep nexit {R} t mo tr.
Arguments tsafe {node} nstep nsafe {R} t mo.
Arguments tpath {node} nstep {R} t mo tr r mo'.
Arguments texit {node} nstep nexit {R} t mo tr.
Arguments leaves_unreachable_m {node} nstep {R} t mo.
Arguments ebind {node A B} t f.
Arguments enode {node A} n pl.
