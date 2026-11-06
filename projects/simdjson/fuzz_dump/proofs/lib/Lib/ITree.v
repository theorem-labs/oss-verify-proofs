(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib.Logic Require Import IndefiniteDescription.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import PropExec MState Mem Exec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition resp := SyscallEffect.
Definition nret (ms : machine_state) (eff : resp) : machine_state :=
  advance_past_svc (apply_effect ms eff).

Lemma nret_svc : forall ms eff, ms_svc_pending (nret ms eff) = None.
Proof. reflexivity. Qed.

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
| Vis (n : node) (k : resp -> itree R)
| Cho (k : Z -> itree R).
Arguments Ret {R} r.
Arguments Vis {R} n k.
Arguments Cho {R} k.

Fixpoint bind {A B} (t : itree A) (f : A -> itree B) : itree B :=
  match t with
  | Ret r => f r
  | Vis n k => Vis n (fun x => bind (k x) f)
  | Cho k => Cho (fun z => bind (k z) f)
  end.

Fixpoint nocho {R} (t : itree R) : Prop :=
  match t with
  | Ret _ => True
  | Vis _ k => forall rsp, nocho (k rsp)
  | Cho _ => False
  end.

Inductive resolves {R} : itree R -> itree R -> Prop :=
| resolves_ret : forall r, resolves (Ret r) (Ret r)
| resolves_vis : forall n k k', (forall rsp, resolves (k' rsp) (k rsp)) -> resolves (Vis n k') (Vis n k)
| resolves_cho : forall k z t', resolves t' (k z) -> resolves t' (Cho k).

Lemma resolves_nocho : forall {R} (t' t : itree R), resolves t' t -> nocho t'.
Proof. intros R t' t H. induction H; cbn; auto. Qed.

Lemma resolves_refl : forall {R} (t : itree R), nocho t -> resolves t t.
Proof.
  intros R t. induction t as [r|n k IH|kc IHc]; intros H; cbn in H; [constructor| |destruct H].
  constructor. intros rsp. apply IH. apply H.
Qed.

Lemma resolves_bind : forall {A B} (t' t : itree A) (f' f : A -> itree B),
  resolves t' t -> (forall a, resolves (f' a) (f a)) -> resolves (bind t' f') (bind t f).
Proof.
  intros A B t' t f' f H Hf. induction H as [r|n k k' Hk IH|k z t'' H IH]; cbn.
  - apply Hf.
  - constructor. intros rsp. apply IH.
  - eapply resolves_cho. exact IH.
Qed.

Lemma nocho_bind : forall {A B} (t : itree A) (f : A -> itree B),
  nocho t -> (forall a, nocho (f a)) -> nocho (bind t f).
Proof.
  intros A B t. induction t as [r|n k IH|kc IHc]; intros f Ht Hf; cbn in *; [apply Hf| |destruct Ht].
  intros rsp. apply IH; [apply Ht| exact Hf].
Qed.

Lemma bind_ret : forall {A B} (r : A) (f : A -> itree B), bind (Ret r) f = f r.
Proof. reflexivity. Qed.

Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Variable at_node : node -> machine_state -> Prop.

Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.

Variable nsafe : node -> Model -> Prop.

Record node_sound : Prop := {

  ns_lazy : forall mo, minv mo -> m_vm_lazy mo = [];

  ns_pending : forall n ms, at_node n ms -> ms_svc_pending ms <> None;

  ns_complete : forall n ms mo evs X, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      sstep_cfg segs cfg (mkCfg ms mo) evs X ->
        (exists rsp mo', X = SNext (mkCfg (nret ms rsp) mo') /\ nstep n mo rsp mo' evs)
     \/ (exists code mo', X = SNext (mkCfg ms mo') /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')]);

  ns_sound : forall n ms mo rsp mo' evs, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nstep n mo rsp mo' evs ->
      m_halted mo' = None /\ minv mo'
      /\ sstep_cfg segs cfg (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo'));
  ns_exit : forall n ms mo code mo', at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nexit n mo code mo' ->
      m_halted mo' = Some code /\ sstep_cfg segs cfg (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo'));

  ns_progress : forall n ms mo, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      (exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo')
}.

Fixpoint impl {R} (t : itree R) (Q : R -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match t with
  | Ret r => evt segs (Q r) ms
  | Vis n k => evt segs (fun ms1 => at_node n ms1 /\ forall rsp, impl (k rsp) Q (nret ms1 rsp)) ms
  | Cho k => exists z, impl (k z) Q ms
  end.

Lemma impl_ret_intro : forall {R} (r : R) Q ms, evt segs (Q r) ms -> impl (Ret r) Q ms.
Proof. intros. exact H. Qed.

Lemma impl_cho : forall {R} (k : Z -> itree R) Q ms, (exists z, impl (k z) Q ms) <-> impl (Cho k) Q ms.
Proof. intros. cbn. tauto. Qed.

Lemma impl_cho_intro : forall {R} z (k : Z -> itree R) Q ms, impl (k z) Q ms -> impl (Cho k) Q ms.
Proof. intros R z k Q ms H. cbn. exists z. exact H. Qed.

Lemma impl_mono : forall {R} (t : itree R) (Q Q' : R -> machine_state -> Prop) ms,
  impl t Q ms -> (forall r ms', Q r ms' -> Q' r ms') -> impl t Q' ms.
Proof.
  induction t as [r|n k IH|kc IHc]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_mono; eauto.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. eapply IH; eauto.
  - destruct H as [z H]. exists z. eapply IHc; eauto.
Qed.

Lemma impl_msteps : forall {R} (t : itree R) Q ms ms',
  msteps segs ms ms' -> impl t Q ms' -> impl t Q ms.
Proof.
  induction t as [r|n k IH|kc IHc]; intros Q ms ms' Hm H; cbn in *.
  - destruct H as (ms2 & H2 & HQ). exists ms2. split; [eapply msteps_trans; eassumption| exact HQ].
  - destruct H as (ms2 & H2 & HQ). exists ms2. split; [eapply msteps_trans; eassumption| exact HQ].
  - destruct H as [z H]. exists z. eapply IHc; eassumption.
Qed.

Lemma impl_evt : forall {R} (t : itree R) Q P ms,
  evt segs P ms -> (forall ms', P ms' -> impl t Q ms') -> impl t Q ms.
Proof.
  intros R t Q P ms (ms' & Hm & HP) K. eapply impl_msteps; [exact Hm|]. exact (K _ HP).
Qed.

Lemma impl_bind : forall {A B} (t : itree A) (f : A -> itree B) Q1 Q ms,
  impl t Q1 ms -> (forall r ms', Q1 r ms' -> impl (f r) Q ms') -> impl (bind t f) Q ms.
Proof.
  induction t as [r|n k IH|kc IHc]; intros f Q1 Q ms H Hf; cbn [bind].
  - cbn in H. eapply impl_evt; [exact H|]. intros ms' HQ. exact (Hf _ _ HQ).
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
  - cbn in H |- *. destruct H as [z H]. exists z. eapply IHc; eauto.
Qed.

Lemma impl_bind_inv : forall {A B} (t : itree A) (f : A -> itree B) Q ms,
  impl (bind t f) Q ms -> impl t (fun r ms' => impl (f r) Q ms') ms.
Proof.
  induction t as [r|n k IH|kc IHc]; intros f Q ms H; cbn [bind] in H; cbn.
  - apply evt_done. exact H.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
  - destruct H as [z H]. exists z. apply IHc. exact H.
Qed.

Fixpoint ttrace {R} (t : itree R) (mo : Model) (tr : list event) : Prop :=
  match t with
  | Ret _ => tr = []
  | Vis n k => (exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')])
            \/ (exists rsp mo' evs tr', nstep n mo rsp mo' evs /\ ttrace (k rsp) mo' tr' /\ tr = evs ++ tr')
  | Cho k => exists z, ttrace (k z) mo tr
  end.

Fixpoint tsafe {R} (t : itree R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> tsafe (k rsp) mo'
  | Cho k => forall z, tsafe (k z) mo
  end.

Fixpoint tpath {R} (t : itree R) (mo : Model) (tr : list event) (r : R) (mo' : Model) : Prop :=
  match t with
  | Ret r0 => r0 = r /\ mo' = mo /\ tr = []
  | Vis n k => exists rsp mo1 evs tr', nstep n mo rsp mo1 evs /\ tpath (k rsp) mo1 tr' r mo' /\ tr = evs ++ tr'
  | Cho k => exists z, tpath (k z) mo tr r mo'
  end.

Fixpoint texit {R} (t : itree R) (mo : Model) (tr : list event) : Prop :=
  match t with
  | Ret _ => False
  | Vis n k => (exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')])
            \/ (exists rsp mo' evs tr', nstep n mo rsp mo' evs /\ texit (k rsp) mo' tr' /\ tr = evs ++ tr')
  | Cho k => exists z, texit (k z) mo tr
  end.

Lemma ttrace_split : forall {R} (t : itree R) mo tr,
  ttrace t mo tr <-> texit t mo tr \/ exists r mo', tpath t mo tr r mo'.
Proof.
  intros R t. induction t as [r|n k IH|kc IHc]; intros mo tr; cbn; cycle 2.
  { split.
    - intros [z Hz]. destruct (proj1 (IHc z mo tr) Hz) as [Hx|(r & mo' & Hp)]; [left; exists z; exact Hx| right; exists r, mo', z; exact Hp].
    - intros [[z Hx]|(r & mo' & z & Hp)]; exists z; apply (proj2 (IHc z mo tr)); [left; exact Hx| right; exists r, mo'; exact Hp]. }
  - split.
    + intros ->. right. exists r, mo. repeat split; reflexivity.
    + intros [F|(r' & mo' & _ & _ & ->)]; [destruct F|reflexivity].
  - split.
    + intros [Hex|(rsp & mo' & evs & tr' & Hst & Ht & ->)]; [left; left; exact Hex|].
      destruct (proj1 (IH rsp mo' tr') Ht) as [Hx|(r & mo'' & Hp)].
      * left; right. exists rsp, mo', evs, tr'. repeat split; assumption.
      * right. exists r, mo'', rsp, mo', evs, tr'. repeat split; assumption.
    + intros [[Hex|(rsp & mo' & evs & tr' & Hst & Hx & ->)]|(r & mo'' & rsp & mo' & evs & tr' & Hst & Hp & ->)].
      * left; exact Hex.
      * right. exists rsp, mo', evs, tr'. split; [assumption|]; split; [|reflexivity]. apply (proj2 (IH rsp mo' tr')). left; exact Hx.
      * right. exists rsp, mo', evs, tr'. split; [assumption|]; split; [|reflexivity]. apply (proj2 (IH rsp mo' tr')). right; eauto.
Qed.

Lemma tpath_bind : forall {A B} (t : itree A) (f : A -> itree B) mo tr rb mo',
  tpath (bind t f) mo tr rb mo' <->
  exists tr1 r mo1 tr2, tpath t mo tr1 r mo1 /\ tpath (f r) mo1 tr2 rb mo' /\ tr = tr1 ++ tr2.
Proof.
  intros A B t. induction t as [r|n k IH|kc IHc]; intros f mo tr rb mo'; cbn; cycle 2.
  { split.
    - intros [z Hz]. destruct (proj1 (IHc z f mo tr rb mo') Hz) as (tr1 & r & mo1 & tr2 & H1 & H2 & E).
      exists tr1, r, mo1, tr2. split; [exists z; exact H1| split; [exact H2| exact E]].
    - intros (tr1 & r & mo1 & tr2 & [z H1] & H2 & E). exists z. apply (proj2 (IHc z f mo tr rb mo')).
      exists tr1, r, mo1, tr2. repeat split; assumption. }
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

Lemma texit_bind : forall {A B} (t : itree A) (f : A -> itree B) mo tr,
  texit (bind t f) mo tr <->
  texit t mo tr \/ exists tr1 r mo1 tr2, tpath t mo tr1 r mo1 /\ texit (f r) mo1 tr2 /\ tr = tr1 ++ tr2.
Proof.
  intros A B t. induction t as [r|n k IH|kc IHc]; intros f mo tr; cbn; cycle 2.
  { split.
    - intros [z Hz]. destruct (proj1 (IHc z f mo tr) Hz) as [Hx|(tr1 & r & mo1 & tr2 & H1 & H2 & E)].
      + left. exists z. exact Hx.
      + right. exists tr1, r, mo1, tr2. split; [exists z; exact H1| split; [exact H2| exact E]].
    - intros [[z Hx]|(tr1 & r & mo1 & tr2 & [z H1] & H2 & E)]; exists z; apply (proj2 (IHc z f mo tr)).
      + left. exact Hx.
      + right. exists tr1, r, mo1, tr2. repeat split; assumption. }
  - split.
    + intros H. right. exists [], r, mo, tr. repeat split; auto.
    + intros [F|(tr1 & r0 & mo1 & tr2 & (-> & -> & ->) & H & ->)]; [destruct F|exact H].
  - split.
    + intros [Hex|(rsp & mo1 & evs & tr' & Hst & Hx & ->)]; [left; left; exact Hex|].
      destruct (proj1 (IH rsp f mo1 tr') Hx) as [H|(tr1 & r & mo2 & tr2 & H1 & H2 & ->)].
      * left; right. exists rsp, mo1, evs, tr'. repeat split; assumption.
      * right. exists (evs ++ tr1), r, mo2, tr2. split; [idtac|split; [exact H2|apply app_assoc]].
        exists rsp, mo1, evs, tr1. repeat split; assumption.
    + intros [[Hex|(rsp & mo1 & evs & tr' & Hst & Hx & ->)]|(tr1 & r & mo2 & tr2 & (rsp & mo1 & evs & tr' & Hst & H1 & ->) & H2 & ->)].
      * left; exact Hex.
      * right. exists rsp, mo1, evs, tr'. split; [assumption|split; [idtac|reflexivity]].
        apply (proj2 (IH rsp f mo1 tr')). left; exact Hx.
      * right. exists rsp, mo1, evs, (tr' ++ tr2). split; [assumption|split; [idtac|symmetry; apply app_assoc]].
        apply (proj2 (IH rsp f mo1 _)). right. exists tr', r, mo2, tr2. repeat split; assumption.
Qed.

Lemma ttrace_bind : forall {A B} (t : itree A) (f : A -> itree B) mo tr,
  ttrace (bind t f) mo tr <->
  texit t mo tr \/ exists tr1 r mo1 tr2, tpath t mo tr1 r mo1 /\ ttrace (f r) mo1 tr2 /\ tr = tr1 ++ tr2.
Proof.
  intros A B t f mo tr. rewrite ttrace_split, texit_bind. split.
  - intros [[Hx|(tr1 & r & mo1 & tr2 & H1 & H2 & ->)]|(rb & mo' & Hp)].
    + left; exact Hx.
    + right. exists tr1, r, mo1, tr2. split; [assumption|split; [|reflexivity]]. apply ttrace_split. left; exact H2.
    + destruct (proj1 (tpath_bind t f mo tr rb mo') Hp) as (tr1 & r & mo1 & tr2 & H1 & H2 & ->).
      right. exists tr1, r, mo1, tr2. split; [assumption|split; [|reflexivity]]. apply ttrace_split. right; eauto.
  - intros [Hx|(tr1 & r & mo1 & tr2 & H1 & H2 & ->)].
    + left; left; exact Hx.
    + destruct (proj1 (ttrace_split _ _ _) H2) as [Hx|(rb & mo' & Hp)].
      * left; right. exists tr1, r, mo1, tr2. repeat split; assumption.
      * right. exists rb, mo'. apply (proj2 (tpath_bind t f mo _ rb mo')). exists tr1, r, mo1, tr2. repeat split; assumption.
Qed.

Lemma tsafe_bind : forall {A B} (t : itree A) (f : A -> itree B) mo,
  tsafe (bind t f) mo <->
  tsafe t mo /\ (forall tr r mo', tpath t mo tr r mo' -> tsafe (f r) mo').
Proof.
  intros A B t. induction t as [r|n k IH|kc IHc]; intros f mo; cbn in *; cycle 2.
  { split.
    - intros H. split.
      + intros z. exact (proj1 (proj1 (IHc z f mo) (H z))).
      + intros tr r mo' [z Hp]. exact (proj2 (proj1 (IHc z f mo) (H z)) tr r mo' Hp).
    - intros [Hs Hf] z. apply (proj2 (IHc z f mo)). split; [exact (Hs z)|].
      intros tr r mo' Hp. apply (Hf tr r mo'). exists z. exact Hp. }
  - split.
    + intros H. split; [exact I|]. intros tr r0 mo' (<- & -> & _). exact H.
    + intros [_ H]. apply (H [] r mo). repeat split; reflexivity.
  - split.
    + intros [Hn Hk]. split.
      * split; [exact Hn|]. intros rsp mo' evs Hst. exact (proj1 (proj1 (IH rsp f mo') (Hk _ _ _ Hst))).
      * intros tr r mo' (rsp & mo1 & evs & tr' & Hst & Hp & ->).
        exact (proj2 (proj1 (IH rsp f mo1) (Hk _ _ _ Hst)) tr' r mo' Hp).
    + intros [[Hn Hk] Hf]. split; [exact Hn|]. intros rsp mo' evs Hst.
      apply (proj2 (IH rsp f mo')). split; [eapply Hk; eassumption|].
      intros tr r mo'' Hp. apply (Hf (evs ++ tr)). exists rsp, mo', evs, tr. repeat split; assumption.
Qed.

Definition leaves_unreachable {R} (t : itree R) (ms : machine_state) : Prop :=
  impl t (fun _ _ => False) ms.

Definition leaves_unreachable_m {R} (t : itree R) (mo : Model) : Prop :=
  forall tr r mo', tpath t mo tr r mo' -> False.

Lemma leaves_unreachable_m_ret : forall {R} (r : R) mo, leaves_unreachable_m (Ret r) mo -> False.
Proof. intros R r mo H. apply (H [] r mo). cbn. repeat split; reflexivity. Qed.

Lemma leaves_unreachable_m_step : forall {R} n (k : resp -> itree R) mo rsp mo' evs,
  leaves_unreachable_m (Vis n k) mo -> nstep n mo rsp mo' evs -> leaves_unreachable_m (k rsp) mo'.
Proof.
  intros R n k mo rsp mo' evs H Hst tr r mo'' Hp. apply (H (evs ++ tr) r mo''). cbn.
  exists rsp, mo', evs, tr. repeat split; assumption.
Qed.

Lemma leaves_unreachable_impl_m : forall {R} (t : itree R) ms mo,
  nocho t -> leaves_unreachable t ms -> leaves_unreachable_m t mo.
Proof.
  intros R t. induction t as [r|n k IH|kc IHc]; intros ms mo Hnc Ht tr r' mo' Hp; cbn in *.
  - destruct Ht as (ms' & _ & F). destruct F.
  - destruct Ht as (ms1 & _ & _ & Hk). destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
    exact (IH rsp (nret ms1 rsp) mo1 (Hnc rsp) (Hk rsp) tr' r' mo' Hp).
  - destruct Hnc.
Qed.

Lemma tsafe_trivial : (forall n mo, nsafe n mo) -> forall {R} (t : itree R) mo, tsafe t mo.
Proof. intros Hall R t. induction t as [r|n k IH|kc IHc]; intros mo; cbn; [exact I| |intros z; apply IHc]. split; [apply Hall|]. intros; apply IH. Qed.

Lemma tsafe_cho : forall {R} (k : Z -> itree R) mo, tsafe (Cho k) mo <-> forall z, tsafe (k z) mo.
Proof. intros. cbn. tauto. Qed.

Lemma leaves_unreachable_m_cho : forall {R} (k : Z -> itree R) mo,
  leaves_unreachable_m (Cho k) mo <-> forall z, leaves_unreachable_m (k z) mo.
Proof.
  intros R k mo. unfold leaves_unreachable_m. cbn. split.
  - intros H z tr r mo' Hp. apply (H tr r mo'). exists z. exact Hp.
  - intros H tr r mo' [z Hp]. exact (H z tr r mo' Hp).
Qed.

Lemma tsafe_resolves : forall {R} (t' t : itree R), resolves t' t -> forall mo, tsafe t mo -> tsafe t' mo.
Proof.
  intros R t' t H. induction H as [r|n k k' Hk IH|k z t'' H IH]; intros mo Hs; cbn in *.
  - exact I.
  - destruct Hs as [Hn Hs]. split; [exact Hn|]. intros rsp mo' evs Hst. apply IH. eapply Hs. exact Hst.
  - apply IH. apply Hs.
Qed.

Lemma tpath_resolves : forall {R} (t' t : itree R), resolves t' t -> forall mo tr r mo', tpath t' mo tr r mo' -> tpath t mo tr r mo'.
Proof.
  intros R t' t H. induction H as [r0|n k k' Hk IH|k z t'' H IH]; intros mo tr r mo' Hp; cbn in *.
  - exact Hp.
  - destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & E). exists rsp, mo1, evs, tr'. split; [exact Hst|]. split; [apply IH; exact Hp| exact E].
  - exists z. apply IH. exact Hp.
Qed.

Lemma texit_resolves : forall {R} (t' t : itree R), resolves t' t -> forall mo tr, texit t' mo tr -> texit t mo tr.
Proof.
  intros R t' t H. induction H as [r0|n k k' Hk IH|k z t'' H IH]; intros mo tr Hx; cbn in *.
  - exact Hx.
  - destruct Hx as [Hx|(rsp & mo1 & evs & tr' & Hst & Hx & E)]; [left; exact Hx|].
    right. exists rsp, mo1, evs, tr'. split; [exact Hst|]. split; [apply IH; exact Hx| exact E].
  - exists z. apply IH. exact Hx.
Qed.

Lemma ttrace_resolves : forall {R} (t' t : itree R), resolves t' t -> forall mo tr, ttrace t' mo tr -> ttrace t mo tr.
Proof.
  intros R t' t H mo tr Ht. apply ttrace_split in Ht. apply ttrace_split.
  destruct Ht as [Hx|(r & mo' & Hp)]; [left; eapply texit_resolves; eassumption| right; exists r, mo'; eapply tpath_resolves; eassumption].
Qed.

Lemma leaves_unreachable_m_resolves : forall {R} (t' t : itree R), resolves t' t ->
  forall mo, leaves_unreachable_m t mo -> leaves_unreachable_m t' mo.
Proof. intros R t' t H mo Hl tr r mo' Hp. exact (Hl tr r mo' (tpath_resolves t' t H mo tr r mo' Hp)). Qed.

Lemma nocho_step : forall {R} n (k : resp -> itree R) rsp, nocho (Vis n k) -> nocho (k rsp).
Proof. intros R n k rsp H. exact (H rsp). Qed.

Theorem impl_resolve : forall {R} (t : itree R) Q ms,
  impl t Q ms -> exists t', resolves t' t /\ impl t' Q ms.
Proof.
  induction t as [r|n k IH|kc IHc]; intros Q ms H; cbn in H.
  - exists (Ret r). split; [constructor| exact H].
  - destruct H as (ms1 & Hm & Hat & Hk).
    destruct (functional_choice (fun rsp t' => resolves t' (k rsp) /\ impl t' Q (nret ms1 rsp)) (fun rsp => IH rsp Q (nret ms1 rsp) (Hk rsp)))
      as [k' Hk'].
    exists (Vis n k'). split.
    + constructor. intros rsp. exact (proj1 (Hk' rsp)).
    + cbn. exists ms1. split; [exact Hm|]. split; [exact Hat|]. intros rsp. exact (proj2 (Hk' rsp)).
  - destruct H as [z H]. destruct (IHc z Q ms H) as (t' & Hr & Ht'). exists t'. split; [eapply resolves_cho; exact Hr| exact Ht'].
Qed.

Lemma tsafe_step : forall {R} n (k : resp -> itree R) mo rsp mo' evs,
  tsafe (Vis n k) mo -> nstep n mo rsp mo' evs -> tsafe (k rsp) mo'.
Proof. intros R n k mo rsp mo' evs [_ Hk] Hst. eapply Hk; eassumption. Qed.

Lemma sstep_mstep_inv : forall ms mo ms' evs X,
  m_vm_lazy mo = [] ->
  mstep segs ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
  evs = [] /\ X = SNext (mkCfg ms' mo).
Proof.
  intros ms mo ms' evs X Hlz [Hsvc Hstep] Hss.
  inversion Hss; subst; try congruence;
  match goal with H : mi_account_step segs ms mo = _ |- _ =>
    rewrite (mi_account_step_no_lazy segs ms mo Hlz) in H; rewrite Hstep in H; inversion H; subst end.
  split; reflexivity.
Qed.

Lemma sstep_not_halted : forall ms mo evs X,
  sstep_cfg segs cfg (mkCfg ms mo) evs X -> m_halted mo = None.
Proof. intros ms mo evs X Hss. inversion Hss; subst; assumption. Qed.

Lemma star_halted_nil : forall ms mo tr c',
  m_halted mo <> None -> star_cfg segs cfg (mkCfg ms mo) tr c' -> tr = [] /\ c' = mkCfg ms mo.
Proof.
  intros ms mo tr c' Hh Hstar. inversion Hstar; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_not_halted; eassumption.
Qed.

Lemma mstep_sstep : forall ms ms' mo,
  m_halted mo = None -> m_vm_lazy mo = [] -> mstep segs ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) [] (SNext (mkCfg ms' mo)).
Proof.
  intros ms ms' mo Hh Hlz [Hsvc Hstep]. apply sstep_cfg_instr; try assumption.
  rewrite (mi_account_step_no_lazy segs ms mo Hlz), Hstep. reflexivity.
Qed.

Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs). eapply star_cfg_step; [exact H| apply star_cfg_refl].
Qed.

Lemma star_cfg_trans : forall c1 t1 c2 t2 c3,
  star_cfg segs cfg c1 t1 c2 -> star_cfg segs cfg c2 t2 c3 -> star_cfg segs cfg c1 (t1 ++ t2) c3.
Proof.
  intros c1 t1 c2 t2 c3 H1 H2. induction H1 as [c|c evs c' tr c'' Hs Hst IH].
  - exact H2.
  - rewrite <- app_assoc. eapply star_cfg_step; [exact Hs| exact (IH H2)].
Qed.

Lemma msteps_star : forall ms ms' mo,
  m_halted mo = None -> m_vm_lazy mo = [] -> msteps segs ms ms' ->
  star_cfg segs cfg (mkCfg ms mo) [] (mkCfg ms' mo).
Proof.
  intros ms ms' mo Hh Hlz Hm. induction Hm as [ms|ms ms1 ms2 H1 H2 IH].
  - apply star_cfg_refl.
  - change ([] : list event) with ([] ++ [] : list event).
    eapply star_cfg_step; [apply mstep_sstep; eassumption| exact IH].
Qed.

Lemma msteps_comparable : forall ms a b,
  msteps segs ms a -> msteps segs ms b -> msteps segs a b \/ msteps segs b a.
Proof.
  intros ms a b Ha; revert b. induction Ha as [ms|ms ms1 ms2 H1 H2 IH]; intros b Hb.
  - left; exact Hb.
  - inversion Hb; subst.
    + right. eapply msteps_cons; eassumption.
    + apply IH. match goal with Hm : mstep segs ms ?x, Hr : msteps segs ?x b |- _ =>
        rewrite (mstep_det segs ms ms1 x H1 Hm); exact Hr end.
Qed.

Lemma msteps_from_svc : forall ms ms',
  msteps segs ms ms' -> ms_svc_pending ms <> None -> ms' = ms.
Proof.
  intros ms ms' Hm Hsvc. inversion Hm; subst; [reflexivity|].
  exfalso. apply Hsvc. eapply mstep_not_svc; eassumption.
Qed.

Lemma msteps_svc_unique : forall ms a b,
  msteps segs ms a -> msteps segs ms b ->
  ms_svc_pending a <> None -> ms_svc_pending b <> None -> a = b.
Proof.
  intros ms a b Ha Hb Hsa Hsb.
  destruct (msteps_comparable ms a b Ha Hb) as [H|H].
  - symmetry. exact (msteps_from_svc a b H Hsa).
  - exact (msteps_from_svc b a H Hsb).
Qed.

Lemma is_prefix_app_l {A} : forall (l l1 l2 : list A),
  is_prefix l1 l2 -> is_prefix (l ++ l1) (l ++ l2).
Proof. induction l; cbn; auto. Qed.

Lemma impl_inv : forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> nocho t ->
  exists n k ms1, t = Vis n k /\ msteps segs ms ms1 /\ at_node n ms1
               /\ forall rsp, impl (k rsp) Q (nret ms1 rsp).
Proof.
  intros R t Q ms mo H Hl Hnc. destruct t as [r|n k|kc]; cbn in H.
  - destruct (leaves_unreachable_m_ret r mo Hl).
  - destruct H as (ms1 & Hm & Hat & Hk). exists n, k, ms1. repeat split; assumption.
  - destruct Hnc.
Qed.

Definition tree_at {R} (t : itree R) Q (ms : machine_state) (mo : Model) : Prop :=
  impl t Q ms /\ leaves_unreachable_m t mo /\ m_halted mo = None /\ minv mo /\ tsafe t mo /\ nocho t.

Lemma tree_at_step : node_sound -> forall {R} n (k : resp -> itree R) Q ms1 mo rsp mo' evs,
  at_node n ms1 -> (forall rsp, impl (k rsp) Q (nret ms1 rsp)) ->
  leaves_unreachable_m (Vis n k) mo -> m_halted mo = None -> minv mo -> tsafe (Vis n k) mo -> nocho (Vis n k) ->
  nstep n mo rsp mo' evs ->
  tree_at (k rsp) Q (nret ms1 rsp) mo' /\ sstep_cfg segs cfg (mkCfg ms1 mo) evs (SNext (mkCfg (nret ms1 rsp) mo')).
Proof.
  intros NS R n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hnc Hst.
  destruct (ns_sound NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (Hh' & Hinv' & Hss).
  split; [|exact Hss]. split; [apply Hk|]. split; [eapply leaves_unreachable_m_step; eassumption|].
  split; [exact Hh'|]. split; [exact Hinv'|]. split; [eapply tsafe_step; eassumption| exact (Hnc rsp)].
Qed.

Lemma ttrace_exists : node_sound -> forall {R} (t : itree R) Q ms mo,
  tree_at t Q ms mo -> exists full, ttrace t mo full.
Proof.
  intros NS R t. induction t as [r|n k IH|kc IHc]; intros Q ms mo HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret r mo Hl).
  - destruct HT as (Ht & Hl & Hh & Hinv & Hsf & Hnc).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    destruct (ns_progress NS n ms1 mo Hat Hh Hinv (proj1 Hsf)) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
    + destruct (tree_at_step NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hnc Hst) as [HT' _].
      destruct (IH rsp Q (nret ms1 rsp) mo' HT') as (full' & Hfull').
      exists (evs ++ full'). cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
    + exists [ExitEv code (m_fs mo')]. cbn. left. exists code, mo'. split; [assumption|reflexivity].
  - destruct HT as (_ & _ & _ & _ & _ & Hnc). destruct Hnc.
Qed.

Lemma impl_sstep_inv : node_sound -> forall {R} (t : itree R) Q ms mo evs X,
  tree_at t Q ms mo ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
     (exists ms', X = SNext (mkCfg ms' mo) /\ evs = [] /\ mstep segs ms ms' /\ tree_at t Q ms' mo)
  \/ (exists n k rsp mo', t = Vis n k /\ at_node n ms /\ X = SNext (mkCfg (nret ms rsp) mo')
        /\ nstep n mo rsp mo' evs /\ tree_at (k rsp) Q (nret ms rsp) mo')
  \/ (exists n k code mo', t = Vis n k /\ at_node n ms /\ X = SNext (mkCfg ms mo')
        /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')] /\ m_halted mo' = Some code).
Proof.
  intros NS R t Q ms mo evs X HT Hss. destruct HT as (Ht & Hl & Hh & Hinv & Hsf & Hnc).
  destruct (impl_inv t Q ms mo Ht Hl Hnc) as (n & k & ms1 & -> & Hm & Hat & Hk).
  inversion Hm; subst.
  -
    destruct (ns_complete NS n ms1 mo evs X Hat Hh Hinv (proj1 Hsf) Hss)
      as [(rsp & mo' & HX & Hst)|(code & mo' & HX & Hex & Hevs)].
    + right; left. destruct (tree_at_step NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hnc Hst) as [HT' _].
      exists n, k, rsp, mo'. split; [reflexivity|]. split; [exact Hat|]. split; [exact HX|]. split; [exact Hst|exact HT'].
    + right; right. destruct (ns_exit NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (Hh' & _).
      exists n, k, code, mo'. repeat split; auto.
  -
    left. match goal with H1 : mstep segs ms ?x, H2 : msteps segs ?x ms1 |- _ =>
      destruct (sstep_mstep_inv ms mo x evs X (ns_lazy NS mo Hinv) H1 Hss) as (-> & ->);
      exists x; split; [reflexivity|]; split; [reflexivity|]; split; [exact H1|];
      split; [cbn; exists ms1; split; [exact H2|]; split; [exact Hat|exact Hk]|];
      split; [exact Hl|]; split; [exact Hh|]; split; [exact Hinv|]; split; [exact Hsf| exact Hnc] end.
Qed.

Definition run_inv {R} Q (c : config) : Prop :=
  (exists t : itree R, tree_at t Q (cfg_ms c) (cfg_model c))
  \/ m_halted (cfg_model c) <> None.

Lemma run_inv_sstep : node_sound -> forall {R} Q c evs X,
  run_inv (R:=R) Q c -> sstep_cfg segs cfg c evs X -> exists c', X = SNext c' /\ run_inv (R:=R) Q c'.
Proof.
  intros NS R Q [ms mo] evs X Hg Hss. destruct Hg as [(t & HT)|Hh]; cbn in *.
  - destruct (impl_sstep_inv NS t Q ms mo evs X HT Hss)
      as [(ms' & -> & _ & _ & HT')|[(n & k & rsp & mo' & _ & _ & -> & _ & HT')
         |(n & k & code & mo' & _ & _ & -> & _ & _ & Hh')]].
    + eexists; split; [reflexivity|]. left. exists t. exact HT'.
    + eexists; split; [reflexivity|]. left. exists (k rsp). exact HT'.
    + eexists; split; [reflexivity|]. right. cbn. congruence.
  - exfalso. apply Hh. eapply sstep_not_halted; eassumption.
Qed.

Lemma run_inv_star : node_sound -> forall {R} Q c tr c',
  star_cfg segs cfg c tr c' -> run_inv (R:=R) Q c -> run_inv (R:=R) Q c'.
Proof.
  intros NS R Q c tr c' Hstar. induction Hstar as [c|c1 evs c2 tr c3 Hss Hstar IH]; intros Hg; [exact Hg|].
  destruct (run_inv_sstep NS Q c1 evs (SNext c2) Hg Hss) as (c2' & E & Hg'). inversion E; subst. auto.
Qed.

Lemma star_ttrace_prefix : node_sound -> forall {R} Q c tr c',
  star_cfg segs cfg c tr c' ->
  forall (t : itree R) ms mo, c = mkCfg ms mo -> tree_at t Q ms mo ->
  exists full, ttrace t mo full /\ is_prefix tr full.
Proof.
  intros NS R Q c tr c' Hstar.
  induction Hstar as [c|c1 evs c2 tr c3 Hss Hstar IH]; intros t ms mo -> HT.
  - destruct (ttrace_exists NS t Q ms mo HT) as (full & Hf).
    exists full. split; [exact Hf| apply is_prefix_nil].
  - destruct (impl_sstep_inv NS t Q ms mo evs (SNext c2) HT Hss)
      as [(ms' & E & -> & _ & HT')|[(n & k & rsp & mo' & -> & Hat & E & Hst & HT')
         |(n & k & code & mo' & -> & Hat & E & Hex & -> & Hh')]]; inversion E; subst.
    + exact (IH t ms' mo eq_refl HT').
    + destruct (IH (k rsp) (nret ms rsp) mo' eq_refl HT') as (full' & Hf' & Hp').
      exists (evs ++ full'). split.
      * cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
      * apply is_prefix_app_l. exact Hp'.
    + destruct (star_halted_nil ms mo' tr c3) as [-> _]; [congruence|exact Hstar|].
      exists [ExitEv code (m_fs mo')]. split.
      * cbn. left. exists code, mo'. split; [assumption|reflexivity].
      * cbn. split; [reflexivity|exact I].
Qed.

Lemma ttrace_star : node_sound -> forall {R} (t : itree R) Q ms mo full,
  ttrace t mo full -> tree_at t Q ms mo ->
  exists c', star_cfg segs cfg (mkCfg ms mo) full c'.
Proof.
  intros NS R t. induction t as [r|n k IH|kc IHc]; intros Q ms mo full Hf HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret r mo Hl).
  - destruct HT as (Ht & Hl & Hh & Hinv & Hsf & Hnc).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    pose proof (msteps_star ms ms1 mo Hh (ns_lazy NS mo Hinv) Hm) as Hs0.
    cbn in Hf. destruct Hf as [(code & mo' & Hex & ->)|(rsp & mo' & evs & tr' & Hst & Hf' & ->)].
    + destruct (ns_exit NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (_ & Hss).
      exists (mkCfg ms1 mo'). change [ExitEv code (m_fs mo')] with ([] ++ [ExitEv code (m_fs mo')]).
      eapply star_cfg_trans; [exact Hs0|]. apply star_cfg_one. exact Hss.
    + destruct (tree_at_step NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hnc Hst) as [HT' Hss].
      destruct (IH rsp Q (nret ms1 rsp) mo' tr' Hf' HT') as (c' & Hs').
      exists c'. change (evs ++ tr') with ([] ++ (evs ++ tr')).
      eapply star_cfg_trans; [exact Hs0|]. eapply star_cfg_step; [exact Hss| exact Hs'].
  - destruct HT as (_ & _ & _ & _ & _ & Hnc). destruct Hnc.
Qed.

Theorem impl_run_traces2 : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo -> nocho t ->
  ms_svc_pending ms = None ->
  forall tr, obs_trace_cfg segs cfg (mkCfg ms mo) tr <-> exists full, ttrace t mo full /\ is_prefix tr full.
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf Hnc _ tr.
  assert (HT : tree_at t Q ms mo) by (repeat split; assumption). split.
  - intros (tr' & c & Hstar & Hp).
    destruct (star_ttrace_prefix NS Q (mkCfg ms mo) tr' c Hstar t ms mo eq_refl HT) as (full & Hf & Hp').
    exists full. split; [exact Hf| eapply is_prefix_trans; eassumption].
  - intros (full & Hf & Hp).
    destruct (ttrace_star NS t Q ms mo full Hf HT) as (c' & Hs).
    exists full, c'. split; assumption.
Qed.

Theorem impl_run_traces3 : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  ms_svc_pending ms = None ->
  exists t', resolves t' t /\
    forall tr, obs_trace_cfg segs cfg (mkCfg ms mo) tr <-> exists full, ttrace t' mo full /\ is_prefix tr full.
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf Hsvc.
  destruct (impl_resolve t Q ms Ht) as (t' & Hr & Ht'). exists t'. split; [exact Hr|].
  apply (impl_run_traces2 NS t' Q ms mo Ht' (leaves_unreachable_m_resolves t' t Hr mo Hl) Hh Hinv
           (tsafe_resolves t' t Hr mo Hsf) (resolves_nocho t' t Hr) Hsvc).
Qed.

Theorem impl_run_safe2 : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  ms_svc_pending ms = None ->
  ~ reaches_error_cfg segs cfg (mkCfg ms mo).
Proof.
  intros NS R t Q ms mo Ht0 Hl0 Hh Hinv Hsf0 _ (tr & c & evs & Hstar & Hss).
  destruct (impl_resolve t Q ms Ht0) as (t' & Hr & Ht).
  pose proof (leaves_unreachable_m_resolves t' t Hr mo Hl0) as Hl. pose proof (tsafe_resolves t' t Hr mo Hsf0) as Hsf.
  pose proof (resolves_nocho t' t Hr) as Hnc.
  assert (Hg : run_inv (R:=R) Q c).
  { eapply run_inv_star; [exact NS|exact Hstar|]. left. exists t'. cbn. repeat split; assumption. }
  destruct (run_inv_sstep NS Q c evs SError Hg Hss) as (c' & E & _). discriminate E.
Qed.

Theorem impl_run_modeled2 : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  ms_svc_pending ms = None ->
  ~ reaches_unmodeled_cfg segs cfg (mkCfg ms mo).
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf Hsvc Hu.
  apply (impl_run_safe2 NS t Q ms mo Ht Hl Hh Hinv Hsf Hsvc).
  apply reaches_unmodeled_cfg_reaches_error_cfg. exact Hu.
Qed.

Theorem impl_run_progress2 : node_sound -> forall {R} (t : itree R) Q ms mo tr ms' mo',
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  star_cfg segs cfg (mkCfg ms mo) tr (mkCfg ms' mo') -> m_halted mo' = None ->
  exists evs c'', sstep_cfg segs cfg (mkCfg ms' mo') evs (SNext c'').
Proof.
  intros NS R t Q ms mo tr ms' mo' Ht0 Hl0 Hh Hinv Hsf0 Hstar Hh'.
  destruct (impl_resolve t Q ms Ht0) as (t0 & Hr & Ht).
  pose proof (leaves_unreachable_m_resolves t0 t Hr mo Hl0) as Hl. pose proof (tsafe_resolves t0 t Hr mo Hsf0) as Hsf.
  pose proof (resolves_nocho t0 t Hr) as Hnc.
  assert (Hg : run_inv (R:=R) Q (mkCfg ms' mo')).
  { eapply run_inv_star; [exact NS|exact Hstar|]. left. exists t0. cbn. repeat split; assumption. }
  destruct Hg as [(t' & Ht' & Hl' & _ & Hinv' & Hsf' & Hnc')|Hc]; cbn in *; [|congruence].
  destruct (impl_inv t' Q ms' mo' Ht' Hl' Hnc') as (n & k & ms1 & -> & Hm & Hat & Hk).
  cbn in Hsf'. destruct Hsf' as [Hns _].
  inversion Hm; subst.
  - destruct (ns_progress NS n ms1 mo' Hat Hh' Hinv' Hns) as [(rsp & mo'' & evs & Hst)|(code & mo'' & Hex)].
    + destruct (ns_sound NS n ms1 mo' rsp mo'' evs Hat Hh' Hinv' Hns Hst) as (_ & _ & Hss). eauto.
    + destruct (ns_exit NS n ms1 mo' code mo'' Hat Hh' Hinv' Hns Hex) as (_ & Hss). eauto.
  - do 2 eexists. apply mstep_sstep; [eassumption| exact (ns_lazy NS _ Hinv') | eassumption].
Qed.

Theorem impl_run_traces : node_sound -> forall {R} (t : itree R) ms mo,
  nocho t -> leaves_unreachable t ms -> m_halted mo = None -> minv mo -> tsafe t mo -> ms_svc_pending ms = None ->
  forall tr, obs_trace_cfg segs cfg (mkCfg ms mo) tr <-> exists full, ttrace t mo full /\ is_prefix tr full.
Proof.
  intros NS R t ms mo Hnc Ht Hh Hinv Hsf. apply (impl_run_traces2 NS t _ ms mo Ht); [| exact Hh| exact Hinv| exact Hsf| exact Hnc].
  eapply leaves_unreachable_impl_m; [exact Hnc| exact Ht].
Qed.

Theorem impl_run_safe : node_sound -> forall {R} (t : itree R) ms mo,
  nocho t -> leaves_unreachable t ms -> m_halted mo = None -> minv mo -> tsafe t mo -> ms_svc_pending ms = None ->
  ~ reaches_error_cfg segs cfg (mkCfg ms mo).
Proof.
  intros NS R t ms mo Hnc Ht. apply (impl_run_safe2 NS t _ ms mo Ht). eapply leaves_unreachable_impl_m; [exact Hnc| exact Ht].
Qed.

Theorem impl_run_modeled : node_sound -> forall {R} (t : itree R) ms mo,
  nocho t -> leaves_unreachable t ms -> m_halted mo = None -> minv mo -> tsafe t mo -> ms_svc_pending ms = None ->
  ~ reaches_unmodeled_cfg segs cfg (mkCfg ms mo).
Proof.
  intros NS R t ms mo Hnc Ht. apply (impl_run_modeled2 NS t _ ms mo Ht). eapply leaves_unreachable_impl_m; [exact Hnc| exact Ht].
Qed.

Lemma impl_run_progress : node_sound -> forall {R} (t : itree R) ms mo tr ms' mo',
  nocho t -> leaves_unreachable t ms -> m_halted mo = None -> minv mo -> tsafe t mo ->
  star_cfg segs cfg (mkCfg ms mo) tr (mkCfg ms' mo') -> m_halted mo' = None ->
  exists evs c'', sstep_cfg segs cfg (mkCfg ms' mo') evs (SNext c'').
Proof.
  intros NS R t ms mo tr ms' mo' Hnc Ht. apply (impl_run_progress2 NS t _ ms mo tr ms' mo' Ht).
  eapply leaves_unreachable_impl_m; [exact Hnc| exact Ht].
Qed.

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
Lemma ebind_ret_unr : forall {A B} (f : A -> itree (exc B)), ebind (Ret Unr) f = Ret Unr.
Proof. reflexivity. Qed.
Lemma ebind_vis : forall {A B} n k (f : A -> itree (exc B)),
  ebind (Vis n k) f = Vis n (fun rsp => ebind (k rsp) f).
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

Lemma tpath_enode : forall {A} n (pl : resp -> option A) mo tr r mo',
  tpath (enode n pl) mo tr r mo' <->
  exists rsp, nstep n mo rsp mo' tr /\ r = match pl rsp with Some a => Ok a | None => Unr end.
Proof.
  intros A n pl mo tr r mo'. cbn. split.
  - intros (rsp & mo1 & evs & tr' & Hst & Hp & ->). exists rsp.
    destruct (pl rsp) as [a|]; cbn in Hp; destruct Hp as (<- & -> & ->); rewrite app_nil_r; split; auto.
  - intros (rsp & Hst & ->). exists rsp, mo', tr, []. split; [exact Hst|]. split; [|symmetry; apply app_nil_r].
    destruct (pl rsp); cbn; repeat split; reflexivity.
Qed.

Lemma texit_enode : forall {A} n (pl : resp -> option A) mo tr,
  texit (enode n pl) mo tr <-> exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')].
Proof.
  intros A n pl mo tr. cbn. split.
  - intros [H|(rsp & mo' & evs & tr' & _ & Hx & _)]; [exact H|]. destruct (pl rsp); destruct Hx.
  - intros H. left. exact H.
Qed.

Lemma tsafe_enode : forall {A} n (pl : resp -> option A) mo,
  tsafe (enode n pl) mo <-> nsafe n mo.
Proof.
  intros A n pl mo. cbn. split; [intros [H _]; exact H|]. intros H. split; [exact H|].
  intros rsp mo' evs _. destruct (pl rsp); exact I.
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

Lemma texit_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo tr,
  texit (ebind t f) mo tr <->
  texit t mo tr \/ exists tr1 a mo1 tr2, tpath t mo tr1 (Ok a) mo1 /\ texit (f a) mo1 tr2 /\ tr = tr1 ++ tr2.
Proof.
  intros A B t f mo tr. unfold ebind. rewrite texit_bind. split.
  - intros [H|(tr1 & [|a] & mo1 & tr2 & H1 & H2 & ->)]; [left; exact H| destruct H2 |].
    right. exists tr1, a, mo1, tr2. repeat split; assumption.
  - intros [H|(tr1 & a & mo1 & tr2 & H1 & H2 & ->)]; [left; exact H|].
    right. exists tr1, (Ok a), mo1, tr2. repeat split; assumption.
Qed.

Lemma ttrace_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo tr,
  ttrace (ebind t f) mo tr <->
  texit t mo tr
  \/ (exists mo', tpath t mo tr Unr mo')
  \/ exists tr1 a mo1 tr2, tpath t mo tr1 (Ok a) mo1 /\ ttrace (f a) mo1 tr2 /\ tr = tr1 ++ tr2.
Proof.
  intros A B t f mo tr. unfold ebind. rewrite ttrace_bind. split.
  - intros [H|(tr1 & [|a] & mo1 & tr2 & H1 & H2 & ->)]; [left; exact H| |].
    + cbn in H2. subst tr2. right; left. exists mo1. rewrite app_nil_r. exact H1.
    + right; right. exists tr1, a, mo1, tr2. repeat split; assumption.
  - intros [H|[(mo' & H)|(tr1 & a & mo1 & tr2 & H1 & H2 & ->)]]; [left; exact H| |].
    + right. exists tr, Unr, mo', []. split; [exact H|]. split; [reflexivity| symmetry; apply app_nil_r].
    + right. exists tr1, (Ok a), mo1, tr2. repeat split; assumption.
Qed.

Lemma tsafe_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo,
  tsafe (ebind t f) mo <->
  tsafe t mo /\ (forall tr a mo', tpath t mo tr (Ok a) mo' -> tsafe (f a) mo').
Proof.
  intros A B t f mo. unfold ebind. rewrite tsafe_bind. split.
  - intros [Ht Hf]. split; [exact Ht|]. intros tr a mo' Hp. exact (Hf tr (Ok a) mo' Hp).
  - intros [Ht Hf]. split; [exact Ht|]. intros tr [|a] mo' Hp; [exact I|]. exact (Hf tr a mo' Hp).
Qed.

Lemma leaves_unreachable_m_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo,
  leaves_unreachable_m (ebind t f) mo <->
  (forall tr mo', tpath t mo tr Unr mo' -> False)
  /\ (forall tr a mo1, tpath t mo tr (Ok a) mo1 -> leaves_unreachable_m (f a) mo1).
Proof.
  intros A B t f mo. unfold leaves_unreachable_m. split.
  - intros H. split.
    + intros tr mo' Hp. apply (H tr Unr mo'). apply tpath_ebind. left. split; [exact Hp|reflexivity].
    + intros tr a mo1 Hp tr2 r mo' Hp2. apply (H (tr ++ tr2) r mo'). apply tpath_ebind. right.
      exists tr, a, mo1, tr2. repeat split; assumption.
  - intros [HU HO] tr r mo' Hp. apply tpath_ebind in Hp.
    destruct Hp as [[Hp ->]|(tr1 & a & mo1 & tr2 & H1 & H2 & ->)].
    + exact (HU _ _ Hp).
    + exact (HO _ _ _ H1 _ _ _ H2).
Qed.

End ITree.

Arguments Ret {node R} r.
Arguments Vis {node R} n k.
Arguments Cho {node R} k.
Arguments nocho {node R} t.
Arguments resolves {node R} _ _.
Arguments impl {node} segs at_node {R} t Q ms.
Arguments ttrace {node} nstep nexit {R} t mo tr.
Arguments tsafe {node} nstep nsafe {R} t mo.
Arguments tpath {node} nstep {R} t mo tr r mo'.
Arguments texit {node} nstep nexit {R} t mo tr.
Arguments leaves_unreachable_m {node} nstep {R} t mo.
Arguments tree_at {node} segs at_node nstep minv nsafe {R} t Q ms mo.
Arguments ebind {node A B} t f.
Arguments enode {node A} n pl.

Lemma tsafe_mono : forall {node : Type} (nstep : node -> Model -> resp -> Model -> list event -> Prop)
    (P P' : node -> Model -> Prop) {R} (t : itree node R) mo,
  (forall n mo, P n mo -> P' n mo) -> tsafe nstep P t mo -> tsafe nstep P' t mo.
Proof.
  intros node nstep P P' R t. induction t as [r|n k IH|kc IHc]; intros mo HP H; cbn in *.
  - exact I.
  - destruct H as [Hn Hk]. split; [exact (HP _ _ Hn)|]. intros rsp mo' evs Hst. exact (IH rsp mo' HP (Hk rsp mo' evs Hst)).
  - intros z. exact (IHc z mo HP (H z)).
Qed.

Lemma tsafe_conj : forall {node : Type} (nstep : node -> Model -> resp -> Model -> list event -> Prop)
    (P P' : node -> Model -> Prop) {R} (t : itree node R) mo,
  tsafe nstep P t mo -> tsafe nstep P' t mo -> tsafe nstep (fun n mo => P n mo /\ P' n mo) t mo.
Proof.
  intros node nstep P P' R t. induction t as [r|n k IH|kc IHc]; intros mo H1 H2; cbn in *.
  - exact I.
  - destruct H1 as [Hn1 Hk1]. destruct H2 as [Hn2 Hk2]. split; [split; assumption|].
    intros rsp mo' evs Hst. exact (IH rsp mo' (Hk1 rsp mo' evs Hst) (Hk2 rsp mo' evs Hst)).
  - intros z. exact (IHc z mo (H1 z) (H2 z)).
Qed.
