(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0.
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
(exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo');

ns_nolazy : forall mo, minv mo -> m_vm_lazy mo = []
}.

Fixpoint impl {R} (t : itree R) (Q : R -> machine_state -> Prop) (ms : machine_state) : Prop :=
match t with
| Ret r => evt segs (Q r) ms
| Vis n k => evt segs (fun ms1 => at_node n ms1 /\ forall rsp, impl (k rsp) Q (nret ms1 rsp)) ms
end.

Lemma impl_ret_intro : forall {R} (r : R) Q ms, evt segs (Q r) ms -> impl (Ret r) Q ms.
Proof. intros. exact H. Qed.

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

Definition leaves_unreachable {R} (t : itree R) (ms : machine_state) : Prop :=
impl t (fun _ _ => False) ms.

Definition leaves_unreachable_m {R} (t : itree R) (mo : Model) : Prop :=
forall tr r mo', tpath t mo tr r mo' -> False.

Lemma sstep_not_halted : forall ms mo evs X,
sstep segs (mkCfg ms mo) evs X -> m_halted mo = None.
Proof. intros ms mo evs X Hss. inversion Hss; subst; assumption. Qed.

Lemma star_halted_nil : forall ms mo tr c',
m_halted mo <> None -> star segs (mkCfg ms mo) tr c' -> tr = [] /\ c' = mkCfg ms mo.
Proof.
intros ms mo tr c' Hh Hstar. inversion Hstar; subst.
- split; reflexivity.
- exfalso. apply Hh. eapply sstep_not_halted; eassumption.
Qed.

Lemma is_prefix_app_l {A} : forall (l l1 l2 : list A),
is_prefix l1 l2 -> is_prefix (l ++ l1) (l ++ l2).
Proof. induction l; cbn; auto. Qed.

Definition tree_at {R} (t : itree R) Q (ms : machine_state) (mo : Model) : Prop :=
impl t Q ms /\ leaves_unreachable_m t mo /\ m_halted mo = None /\ minv mo /\ tsafe t mo.

Definition run_inv {R} Q (c : config) : Prop :=
(exists t : itree R, tree_at t Q (cfg_ms c) (cfg_model c))
\/ m_halted (cfg_model c) <> None.

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
