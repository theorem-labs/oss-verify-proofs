(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Exec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition resp := SyscallEffect.
Definition nret (ms : machine_state) (eff : resp) : machine_state :=
  advance_past_svc (apply_effect ms eff).

Lemma nret_svc : forall ms eff, ms_svc_pending (nret ms eff) = None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Module Exc.
#[universes(template)]
Inductive exc (A : Type) : Type := Unr | Ok (a : A).
Arguments Unr {A}.
Arguments Ok {A} a.
End Exc.
Import Exc.

(* [comment removed for export] *)
Inductive cho : Type := Cho (kind a b : Z).

Section ITree.

(* [comment removed for export] *)
Variable node : Type.

(* [comment removed for export] *)
Inductive itree (R : Type) : Type :=
| Ret (r : R)
| Vis (n : node) (k : resp -> itree R)
| Choice (valid : cho -> Prop) (k : cho -> itree R).
Arguments Ret {R} r.
Arguments Vis {R} n k.
Arguments Choice {R} valid k.

Fixpoint bind {A B} (t : itree A) (f : A -> itree B) : itree B :=
  match t with
  | Ret r => f r
  | Vis n k => Vis n (fun x => bind (k x) f)
  | Choice v k => Choice v (fun a => bind (k a) f)
  end.

Lemma bind_ret : forall {A B} (r : A) (f : A -> itree B), bind (Ret r) f = f r.
Proof. reflexivity. Qed.

Variable segs : list Segment.

(* [comment removed for export] *)
Variable at_node : node -> machine_state -> Prop.

(* [comment removed for export] *)
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.

(* [comment removed for export] *)
Variable nsafe : node -> Model -> Prop.

(* [comment removed for export] *)
Record node_sound : Prop := {
  (* [comment removed for export] *)
  ns_lazy : forall mo, minv mo -> m_vm_lazy mo = [];
  (* [comment removed for export] *)
  ns_pending : forall n ms, at_node n ms -> ms_svc_pending ms <> None;
  (* [comment removed for export] *)
  ns_complete : forall n ms mo evs X, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      sstep segs (mkCfg ms mo) evs X ->
        (exists rsp mo', X = SNext (mkCfg (nret ms rsp) mo') /\ nstep n mo rsp mo' evs)
     \/ (exists code mo', X = SNext (mkCfg ms mo') /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')]);
  (* [comment removed for export] *)
  ns_sound : forall n ms mo rsp mo' evs, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nstep n mo rsp mo' evs ->
      m_halted mo' = None /\ minv mo'
      /\ sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo'));
  ns_exit : forall n ms mo code mo', at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nexit n mo code mo' ->
      m_halted mo' = Some code /\ sstep segs (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo'));
  (* [comment removed for export] *)
  ns_progress : forall n ms mo, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      (exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo')
}.

(* [comment removed for export] *)

Fixpoint impl {R} (t : itree R) (Q : R -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match t with
  | Ret r => evt segs (Q r) ms
  | Vis n k => evt segs (fun ms1 => at_node n ms1 /\ forall rsp, impl (k rsp) Q (nret ms1 rsp)) ms
  | Choice v k => evt segs (fun ms1 => exists a, v a /\ impl (k a) Q ms1) ms
  end.

Lemma impl_choice_intro : forall {R} (v : cho -> Prop) (k : cho -> itree R) Q ms,
  evt segs (fun ms1 => exists a, v a /\ impl (k a) Q ms1) ms -> impl (Choice v k) Q ms.
Proof. intros. exact H. Qed.

Lemma impl_ret_intro : forall {R} (r : R) Q ms, evt segs (Q r) ms -> impl (Ret r) Q ms.
Proof. intros. exact H. Qed.

Lemma impl_mono : forall {R} (t : itree R) (Q Q' : R -> machine_state -> Prop) ms,
  impl t Q ms -> (forall r ms', Q r ms' -> Q' r ms') -> impl t Q' ms.
Proof.
  induction t as [r|n k IH|v k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_mono; eauto.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. eapply IH; eauto.
  - eapply evt_mono; [exact H|]. intros ms1 (a & Hv & Ha). exists a. split; [exact Hv|]. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Lemma impl_evt : forall {R} (t : itree R) Q P ms,
  evt segs P ms -> (forall ms', P ms' -> impl t Q ms') -> impl t Q ms.
Proof.
  intros R t Q P ms H K. destruct t; cbn in *; eapply evt_cut; eauto; intros ms' HP; apply (K _ HP).
Qed.

(* [comment removed for export] *)
Lemma impl_bind : forall {A B} (t : itree A) (f : A -> itree B) Q1 Q ms,
  impl t Q1 ms -> (forall r ms', Q1 r ms' -> impl (f r) Q ms') -> impl (bind t f) Q ms.
Proof.
  induction t as [r|n k IH|v k IH]; intros f Q1 Q ms H Hf; cbn [bind].
  - cbn in H. eapply impl_evt; [exact H|]. intros ms' HQ. exact (Hf _ _ HQ).
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 (a & Hv & Ha). exists a. split; [exact Hv|]. eapply IH; eauto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ttrace {R} (t : itree R) (mo : Model) (tr : list event) : Prop :=
  match t with
  | Ret _ => tr = []
  | Vis n k => (exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')])
            \/ (exists rsp mo' evs tr', nstep n mo rsp mo' evs /\ ttrace (k rsp) mo' tr' /\ tr = evs ++ tr')
  | Choice v k => exists a, v a /\ ttrace (k a) mo tr
  end.

(* [comment removed for export] *)
Fixpoint tsafe {R} (t : itree R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> tsafe (k rsp) mo'
  | Choice v k => forall a, v a -> tsafe (k a) mo
  end.

(* [comment removed for export] *)
Fixpoint tpath {R} (t : itree R) (mo : Model) (tr : list event) (r : R) (mo' : Model) : Prop :=
  match t with
  | Ret r0 => r0 = r /\ mo' = mo /\ tr = []
  | Vis n k => exists rsp mo1 evs tr', nstep n mo rsp mo1 evs /\ tpath (k rsp) mo1 tr' r mo' /\ tr = evs ++ tr'
  | Choice v k => exists a, v a /\ tpath (k a) mo tr r mo'
  end.

Fixpoint texit {R} (t : itree R) (mo : Model) (tr : list event) : Prop :=
  match t with
  | Ret _ => False
  | Vis n k => (exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')])
            \/ (exists rsp mo' evs tr', nstep n mo rsp mo' evs /\ texit (k rsp) mo' tr' /\ tr = evs ++ tr')
  | Choice v k => exists a, v a /\ texit (k a) mo tr
  end.

Lemma ttrace_split : forall {R} (t : itree R) mo tr,
  ttrace t mo tr <-> texit t mo tr \/ exists r mo', tpath t mo tr r mo'.
Proof.
  intros R t. induction t as [r|n k IH|v k IH]; intros mo tr; cbn.
  3:{ split.
      - intros (a & Hv & Ht). destruct (proj1 (IH a mo tr) Ht) as [Hx|(r & mo' & Hp)].
        + left. exists a. split; assumption.
        + right. exists r, mo', a. split; assumption.
      - intros [(a & Hv & Hx)|(r & mo' & a & Hv & Hp)]; exists a; (split; [exact Hv|]); apply (proj2 (IH a mo tr)).
        + left; exact Hx.
        + right; eauto. }
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
  intros A B t. induction t as [r|n k IH|v k IH]; intros f mo tr rb mo'; cbn.
  3:{ split.
      - intros (a & Hv & Hp). destruct (proj1 (IH a f mo tr rb mo') Hp) as (tr1 & r & mo1 & tr2 & H1 & H2 & ->).
        exists tr1, r, mo1, tr2. split; [exists a; split; assumption|]. split; [exact H2|reflexivity].
      - intros (tr1 & r & mo1 & tr2 & (a & Hv & H1) & H2 & ->). exists a. split; [exact Hv|].
        apply (proj2 (IH a f mo _ rb mo')). exists tr1, r, mo1, tr2. repeat split; assumption. }
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
  intros A B t. induction t as [r|n k IH|v k IH]; intros f mo tr; cbn.
  3:{ split.
      - intros (a & Hv & Hx). destruct (proj1 (IH a f mo tr) Hx) as [H|(tr1 & r & mo1 & tr2 & H1 & H2 & ->)].
        + left. exists a. split; assumption.
        + right. exists tr1, r, mo1, tr2. split; [exists a; split; assumption|]. split; [exact H2|reflexivity].
      - intros [(a & Hv & Hx)|(tr1 & r & mo1 & tr2 & (a & Hv & H1) & H2 & ->)]; exists a; (split; [exact Hv|]).
        + apply (proj2 (IH a f mo tr)). left; exact Hx.
        + apply (proj2 (IH a f mo _)). right. exists tr1, r, mo1, tr2. repeat split; assumption. }
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma tsafe_bind : forall {A B} (t : itree A) (f : A -> itree B) mo,
  tsafe (bind t f) mo <->
  tsafe t mo /\ (forall tr r mo', tpath t mo tr r mo' -> tsafe (f r) mo').
Proof.
  intros A B t. induction t as [r|n k IH|v k IH]; intros f mo; cbn in *.
  3:{ split.
      - intros H. split.
        + intros a Hv. exact (proj1 (proj1 (IH a f mo) (H a Hv))).
        + intros tr r mo' (a & Hv & Hp). exact (proj2 (proj1 (IH a f mo) (H a Hv)) tr r mo' Hp).
      - intros [Hs Hf] a Hv. apply (proj2 (IH a f mo)). split; [exact (Hs a Hv)|].
        intros tr r mo' Hp. apply (Hf tr r mo'). exists a. split; assumption. }
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

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition leaves_unreachable {R} (t : itree R) (ms : machine_state) : Prop :=
  impl t (fun _ _ => False) ms.

(* [comment removed for export] *)
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

Lemma leaves_unreachable_m_choice : forall {R} (v : cho -> Prop) (k : cho -> itree R) mo a,
  leaves_unreachable_m (Choice v k) mo -> v a -> leaves_unreachable_m (k a) mo.
Proof. intros R v k mo a H Hv tr r mo' Hp. apply (H tr r mo'). cbn. exists a. split; assumption. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tsafe_trivial : (forall n mo, nsafe n mo) -> forall {R} (t : itree R) mo, tsafe t mo.
Proof. intros Hall R t. induction t as [r|n k IH|v k IH]; intros mo; cbn; [exact I| |intros a _; apply IH]. split; [apply Hall|]. intros; apply IH. Qed.

Lemma tsafe_choice : forall {R} (v : cho -> Prop) (k : cho -> itree R) mo a, tsafe (Choice v k) mo -> v a -> tsafe (k a) mo.
Proof. intros R v k mo a H Hv. exact (H a Hv). Qed.

Lemma tsafe_step : forall {R} n (k : resp -> itree R) mo rsp mo' evs,
  tsafe (Vis n k) mo -> nstep n mo rsp mo' evs -> tsafe (k rsp) mo'.
Proof. intros R n k mo rsp mo' evs [_ Hk] Hst. eapply Hk; eassumption. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_mstep_inv : forall ms mo ms' evs X,
  m_vm_lazy mo = [] ->
  mstep segs ms ms' ->
  sstep segs (mkCfg ms mo) evs X ->
  evs = [] /\ X = SNext (mkCfg ms' mo).
Proof.
  intros ms mo ms' evs X Hlz [Hsvc Hstep] Hss.
  inversion Hss; subst; try congruence;
  match goal with H : mi_account_step segs ms mo = _ |- _ =>
    rewrite (mi_account_step_no_lazy segs ms mo Hlz) in H; rewrite Hstep in H; inversion H; subst end.
  split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sstep_not_halted : forall ms mo evs X,
  sstep segs (mkCfg ms mo) evs X -> m_halted mo = None.
Proof. intros ms mo evs X Hss. inversion Hss; subst; assumption. Qed.

(* [comment removed for export] *)
Lemma star_halted_nil : forall ms mo tr c',
  m_halted mo <> None -> star segs (mkCfg ms mo) tr c' -> tr = [] /\ c' = mkCfg ms mo.
Proof.
  intros ms mo tr c' Hh Hstar. inversion Hstar; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_not_halted; eassumption.
Qed.

(* [comment removed for export] *)
Lemma mstep_sstep : forall ms ms' mo,
  m_halted mo = None -> m_vm_lazy mo = [] -> mstep segs ms ms' ->
  sstep segs (mkCfg ms mo) [] (SNext (mkCfg ms' mo)).
Proof.
  intros ms ms' mo Hh Hlz [Hsvc Hstep]. apply sstep_instr; try assumption.
  rewrite (mi_account_step_no_lazy segs ms mo Hlz), Hstep. reflexivity.
Qed.

Lemma msteps_star : forall ms ms' mo,
  m_halted mo = None -> m_vm_lazy mo = [] -> msteps segs ms ms' ->
  star segs (mkCfg ms mo) [] (mkCfg ms' mo).
Proof.
  intros ms ms' mo Hh Hlz Hm. induction Hm as [ms|ms ms1 ms2 H1 H2 IH].
  - apply star_refl.
  - change ([] : list event) with ([] ++ [] : list event).
    eapply star_step; [apply mstep_sstep; eassumption| exact IH].
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)

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

(* [comment removed for export] *)
Lemma ebind_ret_ok : forall {A B} (a : A) (f : A -> itree (exc B)), ebind (Ret (Ok a)) f = f a.
Proof. reflexivity. Qed.
Lemma ebind_ret_unr : forall {A B} (f : A -> itree (exc B)), ebind (Ret Unr) f = Ret Unr.
Proof. reflexivity. Qed.
Lemma ebind_vis : forall {A B} n k (f : A -> itree (exc B)),
  ebind (Vis n k) f = Vis n (fun rsp => ebind (k rsp) f).
Proof. reflexivity. Qed.
Lemma ebind_choice : forall {A B} v k (f : A -> itree (exc B)),
  ebind (Choice v k) f = Choice v (fun a => ebind (k a) f).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition echoice (v : cho -> Prop) : itree (exc cho) := Choice v (fun a => Ret (Ok a)).

Lemma impl_echoice : forall (v : cho -> Prop) (Q : cho -> machine_state -> Prop) ms,
  evt segs (fun ms1 => exists a, v a /\ Q a ms1) ms -> impl (echoice v) (epost Q) ms.
Proof.
  intros v Q ms H. cbn. eapply evt_mono; [exact H|]. intros ms1 (a & Hv & HQ). exists a. split; [exact Hv|].
  cbn. apply evt_done. exact HQ.
Qed.

Lemma tpath_echoice : forall (v : cho -> Prop) mo tr r mo',
  tpath (echoice v) mo tr r mo' <-> exists a, v a /\ r = Ok a /\ mo' = mo /\ tr = [].
Proof.
  intros v mo tr r mo'. cbn. split.
  - intros (a & Hv & E & -> & ->). exists a. repeat split; auto.
  - intros (a & Hv & -> & -> & ->). exists a. repeat split; auto.
Qed.

Lemma texit_echoice : forall (v : cho -> Prop) mo tr, texit (echoice v) mo tr <-> False.
Proof. intros v mo tr. cbn. split; [intros (a & _ & F); exact F| intros []]. Qed.

Lemma tsafe_echoice : forall (v : cho -> Prop) mo, tsafe (echoice v) mo.
Proof. intros v mo a _. exact I. Qed.

Lemma impl_ret_ok : forall {A} (Q : A -> machine_state -> Prop) a ms,
  evt segs (Q a) ms -> impl (Ret (Ok a)) (epost Q) ms.
Proof. intros A Q a ms H. exact H. Qed.

(* [comment removed for export] *)
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
Arguments Choice {node R} valid k.
Arguments impl {node} segs at_node {R} t Q ms.
Arguments ttrace {node} nstep nexit {R} t mo tr.
Arguments tsafe {node} nstep nsafe {R} t mo.
Arguments tpath {node} nstep {R} t mo tr r mo'.
Arguments texit {node} nstep nexit {R} t mo tr.
Arguments leaves_unreachable_m {node} nstep {R} t mo.
Arguments ebind {node A B} t f.
Arguments enode {node A} n pl.
Arguments echoice {node} v.
