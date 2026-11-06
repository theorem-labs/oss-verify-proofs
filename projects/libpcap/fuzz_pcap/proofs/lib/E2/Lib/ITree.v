(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec.
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

Section ITree.

(* [comment removed for export] *)
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

#[using="Type"] Lemma bind_ret : forall {A B} (r : A) (f : A -> itree B), bind (Ret r) f = f r.
Proof. reflexivity. Qed.

Variable segs : list Segment.

(* [comment removed for export] *)
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
Variable at_node : node -> machine_state -> Prop.

(* [comment removed for export] *)
Variable npeek : node -> option (machine_state -> resp).

(* [comment removed for export] *)
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.

(* [comment removed for export] *)
Variable nsafe : node -> Model -> Prop.

(* [comment removed for export] *)
Record node_sound : Prop := {
  (* [comment removed for export] *)
  ns_nolazy : forall mo, minv mo -> m_vm_lazy mo = [];
  (* [comment removed for export] *)
  ns_pending : forall n ms, at_node n ms -> ms_svc_pending ms <> None;
  (* [comment removed for export] *)
  ns_complete : forall n ms mo evs X, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      sstep_cfg segs cfg (mkCfg ms mo) evs X ->
        (exists rsp mo', X = SNext (mkCfg (nret ms rsp) mo') /\ nstep n mo rsp mo' evs)
     \/ (exists code mo', X = SNext (mkCfg ms mo') /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')]);
  (* [comment removed for export] *)
  ns_sound : forall n ms mo rsp mo' evs, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nstep n mo rsp mo' evs ->
      m_halted mo' = None /\ minv mo'
      /\ sstep_cfg segs cfg (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo'));
  ns_exit : forall n ms mo code mo', at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nexit n mo code mo' ->
      m_halted mo' = Some code /\ sstep_cfg segs cfg (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo'));
  (* [comment removed for export] *)
  ns_progress : forall n ms mo, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      (exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo');
  (* [comment removed for export] *)
  ns_peek : forall n f ms mo, npeek n = Some f -> nstep n mo (f ms) mo [];
  (* [comment removed for export] *)
  ns_peek_at : forall n f ms, npeek n = Some f -> ~ at_node n ms
}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint impl {R} (t : itree R) (Q : R -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match t with
  | Ret r => evt segs (Q r) ms
  | Vis n k =>
      evt segs (fun ms1 =>
           (at_node n ms1 /\ forall rsp, impl (k rsp) Q (nret ms1 rsp))
        \/ (exists f, npeek n = Some f /\ impl (k (f ms1)) Q ms1)) ms
  end.

#[using="Type"] Lemma impl_ret_intro : forall {R} (r : R) Q ms, evt segs (Q r) ms -> impl (Ret r) Q ms.
Proof. intros. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma impl_vis : forall {R} n (k : resp -> itree R) Q ms,
  evt segs (fun ms1 => at_node n ms1 /\ forall rsp, impl (k rsp) Q (nret ms1 rsp)) ms ->
  impl (Vis n k) Q ms.
Proof. intros R n k Q ms H. cbn. eapply evt_mono; [exact H|]. intros ms1 H1. left. exact H1. Qed.

#[using="Type"] Lemma impl_vis_inv : forall {R} n (k : resp -> itree R) Q ms,
  npeek n = None -> impl (Vis n k) Q ms ->
  evt segs (fun ms1 => at_node n ms1 /\ forall rsp, impl (k rsp) Q (nret ms1 rsp)) ms.
Proof.
  intros R n k Q ms Hn H. cbn in H. eapply evt_mono; [exact H|].
  intros ms1 [H1|(f & Hf & _)]; [exact H1|]. rewrite Hn in Hf. discriminate Hf.
Qed.

#[using="Type"] Lemma impl_peek : forall {R} n f (k : resp -> itree R) Q ms,
  npeek n = Some f ->
  evt segs (fun ms1 => impl (k (f ms1)) Q ms1) ms ->
  impl (Vis n k) Q ms.
Proof.
  intros R n f k Q ms Hn H. cbn. eapply evt_mono; [exact H|]. intros ms1 H1. right. exists f. split; [exact Hn|exact H1].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma impl_peek_now : forall {R} n f (k : resp -> itree R) Q ms,
  npeek n = Some f -> impl (k (f ms)) Q ms -> impl (Vis n k) Q ms.
Proof. intros R n f k Q ms Hn H. apply (impl_peek n f k Q ms Hn). apply evt_done. exact H. Qed.

#[using="Type"] Lemma impl_peek_inv : forall {R} n f (k : resp -> itree R) Q ms,
  (forall ms1, npeek n = Some f -> ~ at_node n ms1) ->
  npeek n = Some f -> impl (Vis n k) Q ms ->
  evt segs (fun ms1 => impl (k (f ms1)) Q ms1) ms.
Proof.
  intros R n f k Q ms Hex Hn H. cbn in H. eapply evt_mono; [exact H|].
  intros ms1 [[Hat _]|(f' & Hf' & H1)]; [destruct (Hex ms1 Hn Hat)|].
  rewrite Hn in Hf'. injection Hf' as <-. exact H1.
Qed.

#[using="Type"] Lemma impl_mono : forall {R} (t : itree R) (Q Q' : R -> machine_state -> Prop) ms,
  impl t Q ms -> (forall r ms', Q r ms' -> Q' r ms') -> impl t Q' ms.
Proof.
  induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_mono; eauto.
  - eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(f & Hf & Hk)].
    + left. split; [exact Hat|]. intros rsp. eapply IH; eauto.
    + right. exists f. split; [exact Hf|]. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma impl_cut : forall {R} (t : itree R) (Q Q' : R -> machine_state -> Prop) ms,
  impl t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') -> impl t Q' ms.
Proof.
  induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; eauto.
  - eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(f & Hf & Hk)].
    + left. split; [exact Hat|]. intros rsp. eapply IH; eauto.
    + right. exists f. split; [exact Hf|]. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma impl_evt : forall {R} (t : itree R) Q P ms,
  evt segs P ms -> (forall ms', P ms' -> impl t Q ms') -> impl t Q ms.
Proof.
  intros R t Q P ms H K. destruct t as [r|n k]; cbn in *; eapply evt_cut; eauto; intros ms' HP; apply (K _ HP).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma impl_bind : forall {A B} (t : itree A) (f : A -> itree B) Q1 Q ms,
  impl t Q1 ms -> (forall r ms', Q1 r ms' -> impl (f r) Q ms') -> impl (bind t f) Q ms.
Proof.
  induction t as [r|n k IH]; intros f Q1 Q ms H Hf; cbn [bind].
  - cbn in H. eapply impl_evt; [exact H|]. intros ms' HQ. exact (Hf _ _ HQ).
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)].
    + left. split; [exact Hat|]. intros rsp. eapply IH; eauto.
    + right. exists g. split; [exact Hg|]. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma impl_bind_cong : forall {A B} (t : itree A) (k1 k2 : A -> itree B) (Q : B -> machine_state -> Prop) ms,
  (forall r ms', impl (k1 r) Q ms' -> impl (k2 r) Q ms') ->
  impl (bind t k1) Q ms -> impl (bind t k2) Q ms.
Proof.
  intros A B t. induction t as [r|n k IH]; intros k1 k2 Q ms HK H; cbn [bind] in *.
  - apply HK. exact H.
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)].
    + left. split; [exact Hat|]. intros rsp. eapply IH; [exact HK| apply Hk].
    + right. exists g. split; [exact Hg|]. eapply IH; [exact HK| apply Hk].
Qed.

#[using="Type"] Lemma impl_bind_assoc : forall {A B C} (t : itree A) (g : A -> itree B) (f : B -> itree C) Q ms,
  impl (bind t (fun x => bind (g x) f)) Q ms -> impl (bind (bind t g) f) Q ms.
Proof.
  intros A B C t. induction t as [r|n k IH]; intros g f Q ms H; cbn [bind] in *.
  - exact H.
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(h & Hh & Hk)].
    + left. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
    + right. exists h. split; [exact Hh|]. apply IH. apply Hk.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ttrace {R} (t : itree R) (mo : Model) (tr : list event) : Prop :=
  match t with
  | Ret _ => tr = []
  | Vis n k => (exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')])
            \/ (exists rsp mo' evs tr', nstep n mo rsp mo' evs /\ ttrace (k rsp) mo' tr' /\ tr = evs ++ tr')
  end.

(* [comment removed for export] *)
Fixpoint tsafe {R} (t : itree R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> tsafe (k rsp) mo'
  end.

(* [comment removed for export] *)
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

#[using="Type"] Lemma ttrace_split : forall {R} (t : itree R) mo tr,
  ttrace t mo tr <-> texit t mo tr \/ exists r mo', tpath t mo tr r mo'.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo tr; cbn.
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

#[using="Type"] Lemma tpath_bind : forall {A B} (t : itree A) (f : A -> itree B) mo tr rb mo',
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

#[using="Type"] Lemma texit_bind : forall {A B} (t : itree A) (f : A -> itree B) mo tr,
  texit (bind t f) mo tr <->
  texit t mo tr \/ exists tr1 r mo1 tr2, tpath t mo tr1 r mo1 /\ texit (f r) mo1 tr2 /\ tr = tr1 ++ tr2.
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo tr; cbn.
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
#[using="Type"] Lemma ttrace_bind : forall {A B} (t : itree A) (f : A -> itree B) mo tr,
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
#[using="Type"] Lemma tsafe_bind : forall {A B} (t : itree A) (f : A -> itree B) mo,
  tsafe (bind t f) mo <->
  tsafe t mo /\ (forall tr r mo', tpath t mo tr r mo' -> tsafe (f r) mo').
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo; cbn in *.
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

Inductive wreach {R} : itree R -> Model -> (list event -> R -> Model -> Prop) -> Prop :=
| wreach_ret : forall r mo (P : list event -> R -> Model -> Prop),
    P [] r mo -> wreach (Ret r) mo P
| wreach_vis : forall n k mo (P : list event -> R -> Model -> Prop) rsp mo' evs,
    npeek n = None -> nstep n mo rsp mo' evs ->
    wreach (k rsp) mo' (fun tr => P (evs ++ tr)) -> wreach (Vis n k) mo P
| wreach_peek : forall n k mo (P : list event -> R -> Model -> Prop) f,
    npeek n = Some f ->
    (forall rsp mo' evs, nstep n mo rsp mo' evs -> wreach (k rsp) mo' (fun tr => P (evs ++ tr))) ->
    wreach (Vis n k) mo P.

Inductive wexit {R} : itree R -> Model -> (list event -> Prop) -> Prop :=
| wexit_exit : forall n k mo (T : list event -> Prop) code mo',
    npeek n = None -> nexit n mo code mo' -> T [ExitEv code (m_fs mo')] -> wexit (Vis n k) mo T
| wexit_vis : forall n k mo (T : list event -> Prop) rsp mo' evs,
    npeek n = None -> nstep n mo rsp mo' evs ->
    wexit (k rsp) mo' (fun tr => T (evs ++ tr)) -> wexit (Vis n k) mo T
| wexit_peek : forall n k mo (T : list event -> Prop) f,
    npeek n = Some f ->
    (forall rsp mo' evs, nstep n mo rsp mo' evs -> wexit (k rsp) mo' (fun tr => T (evs ++ tr))) ->
    wexit (Vis n k) mo T.

Inductive wins {R} : itree R -> Model -> (list event -> Prop) -> Prop :=
| wins_nil : forall t mo (T : list event -> Prop), T [] -> wins t mo T
| wins_exit : forall n k mo (T : list event -> Prop) code mo',
    npeek n = None -> nexit n mo code mo' -> T [ExitEv code (m_fs mo')] -> wins (Vis n k) mo T
| wins_vis : forall n k mo (T : list event -> Prop) rsp mo' evs,
    npeek n = None -> nstep n mo rsp mo' evs ->
    wins (k rsp) mo' (fun tr => T (evs ++ tr)) -> wins (Vis n k) mo T
| wins_peek : forall n k mo (T : list event -> Prop) f,
    npeek n = Some f ->
    (forall rsp mo' evs, nstep n mo rsp mo' evs -> wins (k rsp) mo' (fun tr => T (evs ++ tr))) ->
    wins (Vis n k) mo T.

(* [comment removed for export] *)
#[using="Type"] Lemma wreach_mono : forall {R} (t : itree R) mo P P',
  wreach t mo P -> (forall tr r mo', P tr r mo' -> P' tr r mo') -> wreach t mo P'.
Proof.
  intros R t mo P P' H. revert P'. induction H as [r mo P HP|n k mo P rsp mo' evs Hn Hst H IH|n k mo P f Hn H IH]; intros P' HPP'.
  - apply wreach_ret. apply HPP'. exact HP.
  - eapply wreach_vis; [exact Hn|exact Hst|]. apply IH. intros tr r mo''. apply HPP'.
  - eapply wreach_peek; [exact Hn|]. intros rsp mo' evs Hst. apply (IH rsp mo' evs Hst). intros tr r mo''. apply HPP'.
Qed.

#[using="Type"] Lemma wexit_mono : forall {R} (t : itree R) mo T T',
  wexit t mo T -> (forall tr, T tr -> T' tr) -> wexit t mo T'.
Proof.
  intros R t mo T T' H. revert T'. induction H as [n k mo T code mo' Hn Hex HT|n k mo T rsp mo' evs Hn Hst H IH|n k mo T f Hn H IH]; intros T' HTT'.
  - eapply wexit_exit; [exact Hn|exact Hex|]. apply HTT'. exact HT.
  - eapply wexit_vis; [exact Hn|exact Hst|]. apply IH. intros tr. apply HTT'.
  - eapply wexit_peek; [exact Hn|]. intros rsp mo' evs Hst. apply (IH rsp mo' evs Hst). intros tr. apply HTT'.
Qed.

#[using="Type"] Lemma wins_mono : forall {R} (t : itree R) mo T T',
  wins t mo T -> (forall tr, T tr -> T' tr) -> wins t mo T'.
Proof.
  intros R t mo T T' H. revert T'. induction H as [t mo T HT|n k mo T code mo' Hn Hex HT|n k mo T rsp mo' evs Hn Hst H IH|n k mo T f Hn H IH]; intros T' HTT'.
  - apply wins_nil. apply HTT'. exact HT.
  - eapply wins_exit; [exact Hn|exact Hex|]. apply HTT'. exact HT.
  - eapply wins_vis; [exact Hn|exact Hst|]. apply IH. intros tr. apply HTT'.
  - eapply wins_peek; [exact Hn|]. intros rsp mo' evs Hst. apply (IH rsp mo' evs Hst). intros tr. apply HTT'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wexit_wins : forall {R} (t : itree R) mo T, wexit t mo T -> wins t mo T.
Proof.
  intros R t mo T H. induction H as [n k mo T code mo' Hn Hex HT|n k mo T rsp mo' evs Hn Hst H IH|n k mo T f Hn H IH].
  - eapply wins_exit; eassumption.
  - eapply wins_vis; eassumption.
  - eapply wins_peek; [exact Hn|]. exact IH.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wreach_bind : forall {A B} (t : itree A) (f : A -> itree B) mo (P : list event -> B -> Model -> Prop),
  wreach t mo (fun tr1 r mo1 => wreach (f r) mo1 (fun tr2 => P (tr1 ++ tr2))) ->
  wreach (bind t f) mo P.
Proof.
  intros A B t f mo P H.
  remember (fun tr1 r mo1 => wreach (f r) mo1 (fun tr2 => P (tr1 ++ tr2))) as P1 eqn:EP.
  assert (HP1 : forall tr1 r mo1, P1 tr1 r mo1 -> wreach (f r) mo1 (fun tr2 => P (tr1 ++ tr2))) by (subst P1; auto).
  clear EP. revert P HP1.
  induction H as [r mo P0 HP0|n k mo P0 rsp mo' evs Hn Hst H IH|n k mo P0 g Hn H IH]; intros P HP1; cbn [bind].
  - exact (HP1 _ _ _ HP0).
  - eapply wreach_vis; [exact Hn|exact Hst|]. apply IH. intros tr1 r mo1 H1.
    eapply wreach_mono; [exact (HP1 _ _ _ H1)|]. intros tr r' mo''. cbn beta. rewrite app_assoc. exact (fun x => x).
  - eapply wreach_peek; [exact Hn|]. intros rsp mo' evs Hst. apply (IH rsp mo' evs Hst). intros tr1 r mo1 H1.
    eapply wreach_mono; [exact (HP1 _ _ _ H1)|]. intros tr r' mo''. cbn beta. rewrite app_assoc. exact (fun x => x).
Qed.

#[using="Type"] Lemma wexit_bind_l : forall {A B} (t : itree A) (f : A -> itree B) mo T,
  wexit t mo T -> wexit (bind t f) mo T.
Proof.
  intros A B t f mo T H. induction H as [n k mo T code mo' Hn Hex HT|n k mo T rsp mo' evs Hn Hst H IH|n k mo T g Hn H IH]; cbn [bind].
  - eapply wexit_exit; eassumption.
  - eapply wexit_vis; [exact Hn|exact Hst|]. exact IH.
  - eapply wexit_peek; [exact Hn|]. exact IH.
Qed.

#[using="Type"] Lemma wexit_bind_r : forall {A B} (t : itree A) (f : A -> itree B) mo (T : list event -> Prop),
  wreach t mo (fun tr1 r mo1 => wexit (f r) mo1 (fun tr2 => T (tr1 ++ tr2))) ->
  wexit (bind t f) mo T.
Proof.
  intros A B t f mo T H.
  remember (fun tr1 r mo1 => wexit (f r) mo1 (fun tr2 => T (tr1 ++ tr2))) as P1 eqn:EP.
  assert (HP1 : forall tr1 r mo1, P1 tr1 r mo1 -> wexit (f r) mo1 (fun tr2 => T (tr1 ++ tr2))) by (subst P1; auto).
  clear EP. revert T HP1.
  induction H as [r mo P0 HP0|n k mo P0 rsp mo' evs Hn Hst H IH|n k mo P0 g Hn H IH]; intros T HP1; cbn [bind].
  - exact (HP1 _ _ _ HP0).
  - eapply wexit_vis; [exact Hn|exact Hst|]. apply IH. intros tr1 r mo1 H1.
    eapply wexit_mono; [exact (HP1 _ _ _ H1)|]. intros tr. cbn beta. rewrite app_assoc. exact (fun x => x).
  - eapply wexit_peek; [exact Hn|]. intros rsp mo' evs Hst. apply (IH rsp mo' evs Hst). intros tr1 r mo1 H1.
    eapply wexit_mono; [exact (HP1 _ _ _ H1)|]. intros tr. cbn beta. rewrite app_assoc. exact (fun x => x).
Qed.

#[using="Type"] Lemma wins_bind_l : forall {A B} (t : itree A) (f : A -> itree B) mo T,
  wins t mo T -> wins (bind t f) mo T.
Proof.
  intros A B t f mo T H. induction H as [t mo T HT|n k mo T code mo' Hn Hex HT|n k mo T rsp mo' evs Hn Hst H IH|n k mo T g Hn H IH]; cbn [bind].
  - apply wins_nil. exact HT.
  - eapply wins_exit; eassumption.
  - eapply wins_vis; [exact Hn|exact Hst|]. exact IH.
  - eapply wins_peek; [exact Hn|]. exact IH.
Qed.

#[using="Type"] Lemma wins_bind_r : forall {A B} (t : itree A) (f : A -> itree B) mo (T : list event -> Prop),
  wreach t mo (fun tr1 r mo1 => wins (f r) mo1 (fun tr2 => T (tr1 ++ tr2))) ->
  wins (bind t f) mo T.
Proof.
  intros A B t f mo T H.
  remember (fun tr1 r mo1 => wins (f r) mo1 (fun tr2 => T (tr1 ++ tr2))) as P1 eqn:EP.
  assert (HP1 : forall tr1 r mo1, P1 tr1 r mo1 -> wins (f r) mo1 (fun tr2 => T (tr1 ++ tr2))) by (subst P1; auto).
  clear EP. revert T HP1.
  induction H as [r mo P0 HP0|n k mo P0 rsp mo' evs Hn Hst H IH|n k mo P0 g Hn H IH]; intros T HP1; cbn [bind].
  - exact (HP1 _ _ _ HP0).
  - eapply wins_vis; [exact Hn|exact Hst|]. apply IH. intros tr1 r mo1 H1.
    eapply wins_mono; [exact (HP1 _ _ _ H1)|]. intros tr. cbn beta. rewrite app_assoc. exact (fun x => x).
  - eapply wins_peek; [exact Hn|]. intros rsp mo' evs Hst. apply (IH rsp mo' evs Hst). intros tr1 r mo1 H1.
    eapply wins_mono; [exact (HP1 _ _ _ H1)|]. intros tr. cbn beta. rewrite app_assoc. exact (fun x => x).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wreach_bind_inv : forall {A B} (t : itree A) (f : A -> itree B) mo (P : list event -> B -> Model -> Prop),
  wreach (bind t f) mo P ->
  wreach t mo (fun tr1 r mo1 => wreach (f r) mo1 (fun tr2 => P (tr1 ++ tr2))).
Proof.
  intros A B t. induction t as [r0|n k IH]; intros f mo P H; cbn [bind] in H.
  - apply wreach_ret. exact H.
  - inversion H; subst.
    + match goal with Hst : nstep n mo ?rsp ?mo' ?evs, Hw : wreach (bind (k ?rsp) f) ?mo' _ |- _ =>
        eapply wreach_vis; [eassumption|exact Hst|];
        eapply wreach_mono; [exact (IH _ f _ _ Hw)|];
        intros tr1 r mo1 H1; cbn beta in H1 |- *;
        eapply wreach_mono; [exact H1|]; intros tr2 r' mo2; cbn beta; rewrite app_assoc; exact (fun x => x) end.
    + match goal with Hall : forall rsp mo' evs, nstep n mo rsp mo' evs -> wreach (bind (k rsp) f) mo' _ |- _ =>
        eapply wreach_peek; [eassumption|]; intros rsp mo' evs Hst;
        eapply wreach_mono; [exact (IH _ f _ _ (Hall rsp mo' evs Hst))|];
        intros tr1 r mo1 H1; cbn beta in H1 |- *;
        eapply wreach_mono; [exact H1|]; intros tr2 r' mo2; cbn beta; rewrite app_assoc; exact (fun x => x) end.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wreach_tpath : forall {R} (t : itree R) mo P,
  (forall n f mo1, npeek n = Some f -> exists rsp, nstep n mo1 rsp mo1 []) ->
  wreach t mo P -> exists tr r mo', tpath t mo tr r mo' /\ P tr r mo'.
Proof.
  intros R t mo P Hinh H. induction H as [r mo P HP|n k mo P rsp mo' evs Hn Hst H IH|n k mo P f Hn H IH].
  - exists [], r, mo. cbn. repeat split; auto.
  - destruct IH as (tr & r & mo'' & Hp & HP). exists (evs ++ tr), r, mo''. split; [|exact HP].
    cbn. exists rsp, mo', evs, tr. repeat split; assumption.
  - destruct (Hinh n f mo Hn) as (rsp & Hst).
    destruct (IH rsp mo [] Hst) as (tr & r & mo'' & Hp & HP). exists tr, r, mo''. split; [|exact HP].
    cbn. exists rsp, mo, [], tr. repeat split; assumption.
Qed.

#[using="Type"] Lemma wexit_texit : forall {R} (t : itree R) mo T,
  (forall n f mo1, npeek n = Some f -> exists rsp, nstep n mo1 rsp mo1 []) ->
  wexit t mo T -> exists tr, texit t mo tr /\ T tr.
Proof.
  intros R t mo T Hinh H. induction H as [n k mo T code mo' Hn Hex HT|n k mo T rsp mo' evs Hn Hst H IH|n k mo T f Hn H IH].
  - exists [ExitEv code (m_fs mo')]. split; [|exact HT]. cbn. left. exists code, mo'. split; [assumption|reflexivity].
  - destruct IH as (tr & Hx & HT). exists (evs ++ tr). split; [|exact HT].
    cbn. right. exists rsp, mo', evs, tr. repeat split; assumption.
  - destruct (Hinh n f mo Hn) as (rsp & Hst).
    destruct (IH rsp mo [] Hst) as (tr & Hx & HT). exists tr. split; [|exact HT].
    cbn. right. exists rsp, mo, [], tr. repeat split; assumption.
Qed.

(* [comment removed for export] *)

Fixpoint npfree {R} (t : itree R) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => npeek n = None /\ forall rsp, npfree (k rsp)
  end.

#[using="Type"] Lemma npfree_bind : forall {A B} (t : itree A) (f : A -> itree B),
  npfree t -> (forall r, npfree (f r)) -> npfree (bind t f).
Proof.
  intros A B t. induction t as [r|n k IH]; intros f Ht Hf; cbn [bind]; [apply Hf|].
  destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. apply IH; [apply Hk|exact Hf].
Qed.

#[using="Type"] Lemma tpath_wreach : forall {R} (t : itree R) mo tr r mo',
  npfree t -> tpath t mo tr r mo' ->
  wreach t mo (fun tr' r' mo'' => tr' = tr /\ r' = r /\ mo'' = mo').
Proof.
  intros R t. induction t as [r0|n k IH]; intros mo tr r mo' Hnp Hp; cbn in Hp.
  - destruct Hp as (-> & -> & ->). apply wreach_ret. repeat split; reflexivity.
  - destruct Hnp as [Hn Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & ->).
    eapply wreach_vis; [exact Hn|exact Hst|]. eapply wreach_mono; [exact (IH rsp mo1 tr' r mo' (Hk rsp) Hp)|].
    intros tr0 r' mo'' (-> & -> & ->). repeat split; reflexivity.
Qed.

#[using="Type"] Lemma texit_wexit : forall {R} (t : itree R) mo tr,
  npfree t -> texit t mo tr -> wexit t mo (eq tr).
Proof.
  intros R t. induction t as [r0|n k IH]; intros mo tr Hnp Hx; cbn in Hx; [destruct Hx|].
  destruct Hnp as [Hn Hk]. destruct Hx as [(code & mo' & Hex & ->)|(rsp & mo' & evs & tr' & Hst & Hx & ->)].
  - eapply wexit_exit; [exact Hn|exact Hex|reflexivity].
  - eapply wexit_vis; [exact Hn|exact Hst|]. eapply wexit_mono; [exact (IH rsp mo' tr' (Hk rsp) Hx)|].
    intros tr0 <-. reflexivity.
Qed.

#[using="Type"] Lemma ttrace_wins : forall {R} (t : itree R) mo tr,
  npfree t -> ttrace t mo tr -> wins t mo (eq tr).
Proof.
  intros R t. induction t as [r0|n k IH]; intros mo tr Hnp Hf; cbn in Hf.
  - subst tr. apply wins_nil. reflexivity.
  - destruct Hnp as [Hn Hk]. destruct Hf as [(code & mo' & Hex & ->)|(rsp & mo' & evs & tr' & Hst & Hf & ->)].
    + eapply wins_exit; [exact Hn|exact Hex|reflexivity].
    + eapply wins_vis; [exact Hn|exact Hst|]. eapply wins_mono; [exact (IH rsp mo' tr' (Hk rsp) Hf)|].
      intros tr0 <-. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition leaves_unreachable {R} (t : itree R) (ms : machine_state) : Prop :=
  impl t (fun _ _ => False) ms.

(* [comment removed for export] *)
Definition leaves_unreachable_m {R} (t : itree R) (mo : Model) : Prop :=
  forall tr r mo', tpath t mo tr r mo' -> False.

#[using="Type"] Lemma leaves_unreachable_m_ret : forall {R} (r : R) mo, leaves_unreachable_m (Ret r) mo -> False.
Proof. intros R r mo H. apply (H [] r mo). cbn. repeat split; reflexivity. Qed.

#[using="Type"] Lemma leaves_unreachable_m_step : forall {R} n (k : resp -> itree R) mo rsp mo' evs,
  leaves_unreachable_m (Vis n k) mo -> nstep n mo rsp mo' evs -> leaves_unreachable_m (k rsp) mo'.
Proof.
  intros R n k mo rsp mo' evs H Hst tr r mo'' Hp. apply (H (evs ++ tr) r mo''). cbn.
  exists rsp, mo', evs, tr. repeat split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ttrace_texit : forall {R} (t : itree R) mo tr,
  leaves_unreachable_m t mo -> ttrace t mo tr -> texit t mo tr.
Proof.
  intros R t mo tr Hl Hf. destruct (proj1 (ttrace_split t mo tr) Hf) as [Hx|(r & mo' & Hp)]; [exact Hx|].
  destruct (Hl tr r mo' Hp).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma leaves_unreachable_impl_m : forall {R} (t : itree R) ms mo,
  npfree t -> leaves_unreachable t ms -> leaves_unreachable_m t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros ms mo Hnp Ht tr r' mo' Hp; cbn in *.
  - destruct Ht as (ms' & _ & F). destruct F.
  - destruct Hnp as [Hn Hk].
    destruct Ht as (ms1 & _ & [[_ Hk']|(f & Hf & _)]); [|rewrite Hn in Hf; discriminate Hf].
    destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
    exact (IH rsp (nret ms1 rsp) mo1 (Hk rsp) (Hk' rsp) tr' r' mo' Hp).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tsafe_trivial : (forall n mo, nsafe n mo) -> forall {R} (t : itree R) mo, tsafe t mo.
Proof. intros Hall R t. induction t as [r|n k IH]; intros mo; cbn; [exact I|]. split; [apply Hall|]. intros; apply IH. Qed.

#[using="Type"] Lemma tsafe_step : forall {R} n (k : resp -> itree R) mo rsp mo' evs,
  tsafe (Vis n k) mo -> nstep n mo rsp mo' evs -> tsafe (k rsp) mo'.
Proof. intros R n k mo rsp mo' evs [_ Hk] Hst. eapply Hk; eassumption. Qed.

(* [comment removed for export] *)
Inductive peels {R} (mo : Model) : itree R -> itree R -> Prop :=
| peels_refl : forall t, peels mo t t
| peels_cons : forall n k rsp t', nstep n mo rsp mo [] -> peels mo (k rsp) t' -> peels mo (Vis n k) t'.

#[using="Type"] Lemma peels_ttrace : forall {R} mo (t t' : itree R) tr,
  peels mo t t' -> ttrace t' mo tr -> ttrace t mo tr.
Proof.
  intros R mo t t' tr H. induction H as [t|n k rsp t' Hst H IH]; intros Hf; [exact Hf|].
  cbn. right. exists rsp, mo, [], tr. split; [exact Hst|]. split; [exact (IH Hf)|reflexivity].
Qed.

#[using="Type"] Lemma peels_texit : forall {R} mo (t t' : itree R) tr,
  peels mo t t' -> texit t' mo tr -> texit t mo tr.
Proof.
  intros R mo t t' tr H. induction H as [t|n k rsp t' Hst H IH]; intros Hf; [exact Hf|].
  cbn. right. exists rsp, mo, [], tr. split; [exact Hst|]. split; [exact (IH Hf)|reflexivity].
Qed.

#[using="Type"] Lemma peels_tpath : forall {R} mo (t t' : itree R) tr r mo',
  peels mo t t' -> tpath t' mo tr r mo' -> tpath t mo tr r mo'.
Proof.
  intros R mo t t' tr r mo' H. induction H as [t|n k rsp t' Hst H IH]; intros Hf; [exact Hf|].
  cbn. exists rsp, mo, [], tr. split; [exact Hst|]. split; [exact (IH Hf)|reflexivity].
Qed.

#[using="Type"] Lemma peels_leaves : forall {R} mo (t t' : itree R),
  peels mo t t' -> leaves_unreachable_m t mo -> leaves_unreachable_m t' mo.
Proof.
  intros R mo t t' H. induction H as [t|n k rsp t' Hst H IH]; intros Hl; [exact Hl|].
  apply IH. eapply leaves_unreachable_m_step; eassumption.
Qed.

#[using="Type"] Lemma peels_tsafe : forall {R} mo (t t' : itree R),
  peels mo t t' -> tsafe t mo -> tsafe t' mo.
Proof.
  intros R mo t t' H. induction H as [t|n k rsp t' Hst H IH]; intros Hs; [exact Hs|].
  apply IH. eapply tsafe_step; eassumption.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma star_cfg_one : forall c evs c', sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs). eapply star_cfg_step; [exact H| apply star_cfg_refl].
Qed.

#[using="Type"] Lemma star_cfg_trans : forall c1 t1 c2 t2 c3,
  star_cfg segs cfg c1 t1 c2 -> star_cfg segs cfg c2 t2 c3 -> star_cfg segs cfg c1 (t1 ++ t2) c3.
Proof.
  intros c1 t1 c2 t2 c3 H1 H2. induction H1 as [c|c1 evs c2 tr c3' Hss Hst IH]; [exact H2|].
  rewrite <- app_assoc. eapply star_cfg_step; [exact Hss| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma mi_account_step_nolazy : forall ms mo,
  m_vm_lazy mo = [] ->
  mi_account_step segs ms mo =
    match RiscvSemantics.step segs ms with
    | MachineOk ms' => MachineOk (ms', mo)
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof. intros ms mo Hl. apply mi_account_step_no_lazy. exact Hl. Qed.

#[using="Type"] Lemma sstep_mstep_inv : forall ms mo ms' evs X,
  m_vm_lazy mo = [] ->
  mstep segs ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
  evs = [] /\ X = SNext (mkCfg ms' mo).
Proof.
  intros ms mo ms' evs X Hl [Hsvc Hstep] Hss.
  inversion Hss; subst; try congruence;
  match goal with H : mi_account_step segs ms mo = _ |- _ =>
    rewrite (mi_account_step_nolazy ms mo Hl), Hstep in H; inversion H; subst end.
  split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_not_halted : forall ms mo evs X,
  sstep_cfg segs cfg (mkCfg ms mo) evs X -> m_halted mo = None.
Proof. intros ms mo evs X Hss. inversion Hss; subst; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_halted_nil : forall ms mo tr c',
  m_halted mo <> None -> star_cfg segs cfg (mkCfg ms mo) tr c' -> tr = [] /\ c' = mkCfg ms mo.
Proof.
  intros ms mo tr c' Hh Hstar. inversion Hstar; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_not_halted; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mstep_sstep : forall ms ms' mo,
  m_halted mo = None -> m_vm_lazy mo = [] -> mstep segs ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) [] (SNext (mkCfg ms' mo)).
Proof.
  intros ms ms' mo Hh Hl [Hsvc Hstep]. apply sstep_cfg_instr; [assumption|assumption|].
  rewrite (mi_account_step_nolazy ms mo Hl), Hstep. reflexivity.
Qed.

#[using="Type"] Lemma msteps_star : forall ms ms' mo,
  m_halted mo = None -> m_vm_lazy mo = [] -> msteps segs ms ms' ->
  star_cfg segs cfg (mkCfg ms mo) [] (mkCfg ms' mo).
Proof.
  intros ms ms' mo Hh Hl Hm. induction Hm as [ms|ms ms1 ms2 H1 H2 IH].
  - apply star_cfg_refl.
  - change ([] : list event) with ([] ++ [] : list event).
    eapply star_cfg_step; [apply mstep_sstep; eassumption| exact IH].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_comparable : forall ms a b,
  msteps segs ms a -> msteps segs ms b -> msteps segs a b \/ msteps segs b a.
Proof.
  intros ms a b Ha; revert b. induction Ha as [ms|ms ms1 ms2 H1 H2 IH]; intros b Hb.
  - left; exact Hb.
  - inversion Hb; subst.
    + right. eapply msteps_cons; eassumption.
    + apply IH. match goal with Hm : mstep segs ms ?x, Hr : msteps segs ?x b |- _ =>
        rewrite (mstep_det segs ms ms1 x H1 Hm); exact Hr end.
Qed.

#[using="Type"] Lemma msteps_from_svc : forall ms ms',
  msteps segs ms ms' -> ms_svc_pending ms <> None -> ms' = ms.
Proof.
  intros ms ms' Hm Hsvc. inversion Hm; subst; [reflexivity|].
  exfalso. apply Hsvc. eapply mstep_not_svc; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_svc_unique : forall ms a b,
  msteps segs ms a -> msteps segs ms b ->
  ms_svc_pending a <> None -> ms_svc_pending b <> None -> a = b.
Proof.
  intros ms a b Ha Hb Hsa Hsb.
  destruct (msteps_comparable ms a b Ha Hb) as [H|H].
  - symmetry. exact (msteps_from_svc a b H Hsa).
  - exact (msteps_from_svc b a H Hsb).
Qed.

#[using="Type"] Lemma is_prefix_app_l {A} : forall (l l1 l2 : list A),
  is_prefix l1 l2 -> is_prefix (l ++ l1) (l ++ l2).
Proof. induction l; cbn; auto. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma impl_inv : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo ->
  exists n k ms1, npeek n = None /\ peels mo t (Vis n k)
               /\ msteps segs ms ms1 /\ at_node n ms1
               /\ forall rsp, impl (k rsp) Q (nret ms1 rsp).
Proof.
  intros NS R t. induction t as [r|n k IH]; intros Q ms mo H Hl; cbn in H.
  - destruct (leaves_unreachable_m_ret r mo Hl).
  - destruct H as (msa & Hma & [[Hat Hk]|(f & Hn & Hk)]).
    + exists n, k, msa. split; [|split; [apply peels_refl|]; repeat split; assumption].
      destruct (npeek n) as [f|] eqn:Hn; [|reflexivity]. destruct (ns_peek_at NS n f msa Hn Hat).
    + pose proof (ns_peek NS n f msa mo Hn) as Hst.
      destruct (IH (f msa) Q msa mo Hk (leaves_unreachable_m_step n k mo _ _ _ Hl Hst))
        as (n' & k' & ms1 & Hn' & Hp & Hm & Hat & Hk').
      exists n', k', ms1. split; [exact Hn'|]. split; [eapply peels_cons; [exact Hst|exact Hp]|].
      split; [eapply msteps_trans; eassumption|]. split; [exact Hat|exact Hk'].
Qed.

(* [comment removed for export] *)
Definition tree_at {R} (t : itree R) Q (ms : machine_state) (mo : Model) : Prop :=
  impl t Q ms /\ leaves_unreachable_m t mo /\ m_halted mo = None /\ minv mo /\ tsafe t mo.

#[using="Type"] Lemma tree_at_step : node_sound -> forall {R} n (k : resp -> itree R) Q ms1 mo rsp mo' evs,
  at_node n ms1 -> (forall rsp, impl (k rsp) Q (nret ms1 rsp)) ->
  leaves_unreachable_m (Vis n k) mo -> m_halted mo = None -> minv mo -> tsafe (Vis n k) mo ->
  nstep n mo rsp mo' evs ->
  tree_at (k rsp) Q (nret ms1 rsp) mo' /\ sstep_cfg segs cfg (mkCfg ms1 mo) evs (SNext (mkCfg (nret ms1 rsp) mo')).
Proof.
  intros NS R n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst.
  destruct (ns_sound NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (Hh' & Hinv' & Hss).
  split; [|exact Hss]. split; [apply Hk|]. split; [eapply leaves_unreachable_m_step; eassumption|].
  split; [exact Hh'|]. split; [exact Hinv'|]. eapply tsafe_step; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tree_at_peek : node_sound -> forall {R} n f (k : resp -> itree R) Q msa mo,
  npeek n = Some f -> impl (k (f msa)) Q msa ->
  leaves_unreachable_m (Vis n k) mo -> m_halted mo = None -> minv mo -> tsafe (Vis n k) mo ->
  tree_at (k (f msa)) Q msa mo.
Proof.
  intros NS R n f k Q msa mo Hn Hk Hl Hh Hinv Hsf.
  pose proof (ns_peek NS n f msa mo Hn) as Hst.
  split; [exact Hk|]. split; [eapply leaves_unreachable_m_step; eassumption|].
  split; [exact Hh|]. split; [exact Hinv|]. eapply tsafe_step; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tree_at_inv : node_sound -> forall {R} (t : itree R) Q ms mo,
  tree_at t Q ms mo ->
  exists n k ms1, npeek n = None /\ peels mo t (Vis n k)
               /\ msteps segs ms ms1 /\ at_node n ms1
               /\ (forall rsp, impl (k rsp) Q (nret ms1 rsp))
               /\ tree_at (Vis n k) Q ms mo.
Proof.
  intros NS R t Q ms mo (Ht & Hl & Hh & Hinv & Hsf).
  destruct (impl_inv NS t Q ms mo Ht Hl) as (n & k & ms1 & Hn & Hp & Hm & Hat & Hk).
  exists n, k, ms1. split; [exact Hn|]. split; [exact Hp|]. split; [exact Hm|]. split; [exact Hat|].
  split; [exact Hk|]. split; [|split; [eapply peels_leaves; eassumption|]].
  - apply (impl_vis n k Q ms). exists ms1. split; [exact Hm|]. split; [exact Hat|exact Hk].
  - split; [exact Hh|]. split; [exact Hinv|]. eapply peels_tsafe; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ttrace_exists : node_sound -> forall {R} (t : itree R) Q ms mo,
  tree_at t Q ms mo -> exists full, ttrace t mo full.
Proof.
  intros NS R t. induction t as [r|n k IH]; intros Q ms mo HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret r mo Hl).
  - destruct HT as (Ht & Hl & Hh & Hinv & Hsf). cbn in Ht.
    destruct Ht as (ms1 & Hm & [[Hat Hk]|(f & Hn & Hk)]).
    + destruct (ns_progress NS n ms1 mo Hat Hh Hinv (proj1 Hsf)) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
      * destruct (tree_at_step NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
        destruct (IH rsp Q (nret ms1 rsp) mo' HT') as (full' & Hfull').
        exists (evs ++ full'). cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
      * exists [ExitEv code (m_fs mo')]. cbn. left. exists code, mo'. split; [assumption|reflexivity].
    + pose proof (tree_at_peek NS n f k Q ms1 mo Hn Hk Hl Hh Hinv Hsf) as HT'.
      destruct (IH (f ms1) Q ms1 mo HT') as (full' & Hfull').
      exists ([] ++ full'). cbn. right. exists (f ms1), mo, [], full'.
      split; [exact (ns_peek NS n f ms1 mo Hn)|]. split; [exact Hfull'|reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma impl_sstep_inv : node_sound -> forall {R} n (k : resp -> itree R) Q ms mo evs X,
  npeek n = None ->
  tree_at (Vis n k) Q ms mo ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
     (exists ms', X = SNext (mkCfg ms' mo) /\ evs = [] /\ mstep segs ms ms' /\ tree_at (Vis n k) Q ms' mo)
  \/ (exists rsp mo', at_node n ms /\ X = SNext (mkCfg (nret ms rsp) mo')
        /\ nstep n mo rsp mo' evs /\ tree_at (k rsp) Q (nret ms rsp) mo')
  \/ (exists code mo', at_node n ms /\ X = SNext (mkCfg ms mo')
        /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')] /\ m_halted mo' = Some code).
Proof.
  intros NS R n k Q ms mo evs X Hn HT Hss. destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
  pose proof (impl_vis_inv n k Q ms Hn Ht) as (ms1 & Hm & Hat & Hk).
  inversion Hm; subst.
  - (* [comment removed for export] *)
    destruct (ns_complete NS n ms1 mo evs X Hat Hh Hinv (proj1 Hsf) Hss)
      as [(rsp & mo' & HX & Hst)|(code & mo' & HX & Hex & Hevs)].
    + right; left. destruct (tree_at_step NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
      exists rsp, mo'. split; [exact Hat|]. split; [exact HX|]. split; [exact Hst|exact HT'].
    + right; right. destruct (ns_exit NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (Hh' & _).
      exists code, mo'. repeat split; auto.
  - (* [comment removed for export] *)
    left. match goal with H1 : mstep segs ms ?x, H2 : msteps segs ?x ms1 |- _ =>
      destruct (sstep_mstep_inv ms mo x evs X (ns_nolazy NS mo Hinv) H1 Hss) as (-> & ->);
      exists x; split; [reflexivity|]; split; [reflexivity|]; split; [exact H1|];
      split; [apply (impl_vis n k Q x); exists ms1; split; [exact H2|]; split; [exact Hat|exact Hk]|];
      split; [exact Hl|]; split; [exact Hh|]; split; [exact Hinv|exact Hsf] end.
Qed.

(* [comment removed for export] *)
Definition run_inv {R} Q (c : config) : Prop :=
  (exists t : itree R, tree_at t Q (cfg_ms c) (cfg_model c))
  \/ m_halted (cfg_model c) <> None.

#[using="Type"] Lemma run_inv_sstep : node_sound -> forall {R} Q c evs X,
  run_inv (R:=R) Q c -> sstep_cfg segs cfg c evs X -> exists c', X = SNext c' /\ run_inv (R:=R) Q c'.
Proof.
  intros NS R Q [ms mo] evs X Hg Hss. destruct Hg as [(t & HT)|Hh]; cbn in *.
  - destruct (tree_at_inv NS t Q ms mo HT) as (n & k & _ & Hn & _ & _ & _ & _ & HT0).
    destruct (impl_sstep_inv NS n k Q ms mo evs X Hn HT0 Hss)
      as [(ms' & -> & _ & _ & HT')|[(rsp & mo' & _ & -> & _ & HT')
         |(code & mo' & _ & -> & _ & _ & Hh')]].
    + eexists; split; [reflexivity|]. left. exists (Vis n k). exact HT'.
    + eexists; split; [reflexivity|]. left. exists (k rsp). exact HT'.
    + eexists; split; [reflexivity|]. right. cbn. congruence.
  - exfalso. apply Hh. eapply sstep_not_halted; eassumption.
Qed.

#[using="Type"] Lemma run_inv_star : node_sound -> forall {R} Q c tr c',
  star_cfg segs cfg c tr c' -> run_inv (R:=R) Q c -> run_inv (R:=R) Q c'.
Proof.
  intros NS R Q c tr c' Hstar. induction Hstar as [c|c1 evs c2 tr c3 Hss Hstar IH]; intros Hg; [exact Hg|].
  destruct (run_inv_sstep NS Q c1 evs (SNext c2) Hg Hss) as (c2' & E & Hg'). inversion E; subst. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_ttrace_prefix : node_sound -> forall {R} Q c tr c',
  star_cfg segs cfg c tr c' ->
  forall (t : itree R) ms mo, c = mkCfg ms mo -> tree_at t Q ms mo ->
  exists full, ttrace t mo full /\ is_prefix tr full.
Proof.
  intros NS R Q c tr c' Hstar.
  induction Hstar as [c|c1 evs c2 tr c3 Hss Hstar IH]; intros t ms mo -> HT.
  - destruct (ttrace_exists NS t Q ms mo HT) as (full & Hf).
    exists full. split; [exact Hf| apply is_prefix_nil].
  - destruct (tree_at_inv NS t Q ms mo HT) as (n & k & _ & Hn & Hp & _ & _ & _ & HT0).
    destruct (impl_sstep_inv NS n k Q ms mo evs (SNext c2) Hn HT0 Hss)
      as [(ms' & E & -> & _ & HT')|[(rsp & mo' & Hat & E & Hst & HT')
         |(code & mo' & Hat & E & Hex & -> & Hh')]]; inversion E; subst.
    + destruct (IH (Vis n k) ms' mo eq_refl HT') as (full & Hf & Hpre).
      exists full. split; [eapply peels_ttrace; eassumption|exact Hpre].
    + destruct (IH (k rsp) (nret ms rsp) mo' eq_refl HT') as (full' & Hf' & Hp').
      exists (evs ++ full'). split.
      * eapply peels_ttrace; [eassumption|]. cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
      * apply is_prefix_app_l. exact Hp'.
    + destruct (star_halted_nil ms mo' tr c3) as [-> _]; [congruence|exact Hstar|].
      exists [ExitEv code (m_fs mo')]. split.
      * eapply peels_ttrace; [eassumption|]. cbn. left. exists code, mo'. split; [assumption|reflexivity].
      * cbn. split; [reflexivity|exact I].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wins_star : node_sound -> forall {R} (t : itree R) mo T,
  wins t mo T -> forall Q ms, tree_at t Q ms mo ->
  exists w c', T w /\ star_cfg segs cfg (mkCfg ms mo) w c'.
Proof.
  intros NS R t mo T H.
  induction H as [t mo T HT|n k mo T code mo' Hn Hex HT|n k mo T rsp mo' evs Hn Hst H IH|n k mo T f Hn H IH];
    intros Q ms HTa.
  - exists [], (mkCfg ms mo). split; [exact HT|apply star_cfg_refl].
  - destruct HTa as (Ht & Hl & Hh & Hinv & Hsf).
    pose proof (impl_vis_inv n k Q ms Hn Ht) as (ms1 & Hm & Hat & Hk).
    pose proof (msteps_star ms ms1 mo Hh (ns_nolazy NS mo Hinv) Hm) as Hs0.
    destruct (ns_exit NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (_ & Hss).
    exists [ExitEv code (m_fs mo')], (mkCfg ms1 mo'). split; [exact HT|].
    change [ExitEv code (m_fs mo')] with ([] ++ [ExitEv code (m_fs mo')]).
    eapply star_cfg_trans; [exact Hs0|]. apply star_cfg_one. exact Hss.
  - destruct HTa as (Ht & Hl & Hh & Hinv & Hsf).
    pose proof (impl_vis_inv n k Q ms Hn Ht) as (ms1 & Hm & Hat & Hk).
    pose proof (msteps_star ms ms1 mo Hh (ns_nolazy NS mo Hinv) Hm) as Hs0.
    destruct (tree_at_step NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' Hss].
    destruct (IH Q (nret ms1 rsp) HT') as (w' & c' & HTw & Hs').
    exists (evs ++ w'), c'. split; [exact HTw|].
    change (evs ++ w') with ([] ++ (evs ++ w')).
    eapply star_cfg_trans; [exact Hs0|]. eapply star_cfg_step; [exact Hss| exact Hs'].
  - destruct HTa as (Ht & Hl & Hh & Hinv & Hsf).
    pose proof (impl_peek_inv n f k Q ms (fun ms1 H => ns_peek_at NS n f ms1 H) Hn Ht) as (msa & Hma & Hk).
    pose proof (msteps_star ms msa mo Hh (ns_nolazy NS mo Hinv) Hma) as Hs0.
    pose proof (ns_peek NS n f msa mo Hn) as Hst.
    pose proof (tree_at_peek NS n f k Q msa mo Hn Hk Hl Hh Hinv Hsf) as HT'.
    destruct (IH (f msa) mo [] Hst Q msa HT') as (w' & c' & HTw & Hs').
    exists w', c'. split; [exact HTw|].
    change w' with ([] ++ w'). eapply star_cfg_trans; [exact Hs0|exact Hs'].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Theorem impl_run_sound2 : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  forall tr, obs_trace_cfg segs cfg (mkCfg ms mo) tr -> exists full, ttrace t mo full /\ is_prefix tr full.
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf tr (tr' & c & Hstar & Hp).
  assert (HT : tree_at t Q ms mo) by (repeat split; assumption).
  destruct (star_ttrace_prefix NS Q (mkCfg ms mo) tr' c Hstar t ms mo eq_refl HT) as (full & Hf & Hp').
  exists full. split; [exact Hf| eapply is_prefix_trans; eassumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem impl_run_complete2 : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  forall T, wins t mo T -> exists w c', T w /\ star_cfg segs cfg (mkCfg ms mo) w c'.
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf T Hw.
  apply (wins_star NS t mo T Hw Q ms). repeat split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Corollary impl_run_complete2_obs : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  forall tr, wins t mo (is_prefix tr) -> obs_trace_cfg segs cfg (mkCfg ms mo) tr.
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf tr Hw.
  destruct (impl_run_complete2 NS t Q ms mo Ht Hl Hh Hinv Hsf (is_prefix tr) Hw) as (w & c' & Hp & Hs).
  exists w, c'. split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem impl_run_traces2 : node_sound -> forall {R} (t : itree R) Q ms mo,
  npfree t ->
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  ms_svc_pending ms = None ->
  forall tr, obs_trace_cfg segs cfg (mkCfg ms mo) tr <-> exists full, ttrace t mo full /\ is_prefix tr full.
Proof.
  intros NS R t Q ms mo Hnp Ht Hl Hh Hinv Hsf _ tr. split.
  - apply (impl_run_sound2 NS t Q ms mo Ht Hl Hh Hinv Hsf).
  - intros (full & Hf & Hp).
    apply (impl_run_complete2_obs NS t Q ms mo Ht Hl Hh Hinv Hsf tr).
    eapply wins_mono; [apply ttrace_wins; eassumption|]. intros tr0 <-. exact Hp.
Qed.

#[using="Type"] Theorem impl_run_safe2 : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  ms_svc_pending ms = None ->
  ~ reaches_error_cfg segs cfg (mkCfg ms mo).
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf _ (tr & c & evs & Hstar & Hss).
  assert (Hg : run_inv (R:=R) Q c).
  { eapply run_inv_star; [exact NS|exact Hstar|]. left. exists t. cbn. repeat split; assumption. }
  destruct (run_inv_sstep NS Q c evs SError Hg Hss) as (c' & E & _). discriminate E.
Qed.

#[using="Type"] Theorem impl_run_modeled2 : node_sound -> forall {R} (t : itree R) Q ms mo,
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  ms_svc_pending ms = None ->
  ~ reaches_unmodeled_cfg segs cfg (mkCfg ms mo).
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf Hsvc.
  intros Hu. apply (reaches_unmodeled_cfg_reaches_error_cfg segs cfg) in Hu. revert Hu. eapply impl_run_safe2; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem impl_run_progress2 : node_sound -> forall {R} (t : itree R) Q ms mo tr ms' mo',
  impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
  star_cfg segs cfg (mkCfg ms mo) tr (mkCfg ms' mo') -> m_halted mo' = None ->
  exists evs c'', sstep_cfg segs cfg (mkCfg ms' mo') evs (SNext c'').
Proof.
  intros NS R t Q ms mo tr ms' mo' Ht Hl Hh Hinv Hsf Hstar Hh'.
  assert (Hg : run_inv (R:=R) Q (mkCfg ms' mo')).
  { eapply run_inv_star; [exact NS|exact Hstar|]. left. exists t. cbn. repeat split; assumption. }
  destruct Hg as [(t' & HT')|Hc]; cbn in *; [|congruence].
  destruct (tree_at_inv NS t' Q ms' mo' HT') as (n & k & ms1 & Hn & _ & Hm & Hat & Hk & (_ & _ & _ & Hinv' & Hsf')).
  cbn in Hsf'. destruct Hsf' as [Hns _].
  inversion Hm; subst.
  - destruct (ns_progress NS n ms1 mo' Hat Hh' Hinv' Hns) as [(rsp & mo'' & evs & Hst)|(code & mo'' & Hex)].
    + destruct (ns_sound NS n ms1 mo' rsp mo'' evs Hat Hh' Hinv' Hns Hst) as (_ & _ & Hss). eauto.
    + destruct (ns_exit NS n ms1 mo' code mo'' Hat Hh' Hinv' Hns Hex) as (_ & Hss). eauto.
  - do 2 eexists. apply mstep_sstep; [eassumption|exact (ns_nolazy NS mo' Hinv')|eassumption].
Qed.

(* [comment removed for export] *)

#[using="Type"] Theorem impl_run_traces : node_sound -> forall {R} (t : itree R) ms mo,
  npfree t ->
  leaves_unreachable t ms -> m_halted mo = None -> minv mo -> tsafe t mo -> ms_svc_pending ms = None ->
  forall tr, obs_trace_cfg segs cfg (mkCfg ms mo) tr <-> exists full, ttrace t mo full /\ is_prefix tr full.
Proof.
  intros NS R t ms mo Hnp Ht. apply (impl_run_traces2 NS t _ ms mo Hnp Ht). eapply leaves_unreachable_impl_m; [exact Hnp|exact Ht].
Qed.

#[using="Type"] Theorem impl_run_safe : node_sound -> forall {R} (t : itree R) ms mo,
  npfree t ->
  leaves_unreachable t ms -> m_halted mo = None -> minv mo -> tsafe t mo -> ms_svc_pending ms = None ->
  ~ reaches_error_cfg segs cfg (mkCfg ms mo).
Proof.
  intros NS R t ms mo Hnp Ht. apply (impl_run_safe2 NS t _ ms mo Ht). eapply leaves_unreachable_impl_m; [exact Hnp|exact Ht].
Qed.

#[using="Type"] Theorem impl_run_modeled : node_sound -> forall {R} (t : itree R) ms mo,
  npfree t ->
  leaves_unreachable t ms -> m_halted mo = None -> minv mo -> tsafe t mo -> ms_svc_pending ms = None ->
  ~ reaches_unmodeled_cfg segs cfg (mkCfg ms mo).
Proof.
  intros NS R t ms mo Hnp Ht. apply (impl_run_modeled2 NS t _ ms mo Ht). eapply leaves_unreachable_impl_m; [exact Hnp|exact Ht].
Qed.

#[using="Type"] Lemma impl_run_progress : node_sound -> forall {R} (t : itree R) ms mo tr ms' mo',
  npfree t ->
  leaves_unreachable t ms -> m_halted mo = None -> minv mo -> tsafe t mo ->
  star_cfg segs cfg (mkCfg ms mo) tr (mkCfg ms' mo') -> m_halted mo' = None ->
  exists evs c'', sstep_cfg segs cfg (mkCfg ms' mo') evs (SNext c'').
Proof.
  intros NS R t ms mo tr ms' mo' Hnp Ht. apply (impl_run_progress2 NS t _ ms mo tr ms' mo' Ht).
  eapply leaves_unreachable_impl_m; [exact Hnp|exact Ht].
Qed.

(* [comment removed for export] *)

Definition ebind {A B} (t : itree (exc A)) (f : A -> itree (exc B)) : itree (exc B) :=
  bind t (fun r => match r with Unr => Ret Unr | Ok a => f a end).

Definition epost {A} (Q : A -> machine_state -> Prop) : exc A -> machine_state -> Prop :=
  fun r ms => match r with Unr => True | Ok a => Q a ms end.

#[using="Type"] Lemma impl_ret_unr : forall {A} (Q : A -> machine_state -> Prop) ms, impl (Ret Unr) (epost Q) ms.
Proof. intros A Q ms. cbn. apply evt_done. exact I. Qed.

#[using="Type"] Lemma impl_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) Q1 Q ms,
  impl t (epost Q1) ms -> (forall a ms', Q1 a ms' -> impl (f a) (epost Q) ms') ->
  impl (ebind t f) (epost Q) ms.
Proof.
  intros A B t f Q1 Q ms Ht Hf. unfold ebind. eapply impl_bind; [exact Ht|].
  intros [|a] ms' H'; cbn in H'.
  - apply impl_ret_unr.
  - apply Hf. exact H'.
Qed.

#[using="Type"] Lemma impl_epost_mono : forall {A} (t : itree (exc A)) (Q Q' : A -> machine_state -> Prop) ms,
  impl t (epost Q) ms -> (forall a ms', Q a ms' -> Q' a ms') -> impl t (epost Q') ms.
Proof.
  intros A t Q Q' ms H HQ. eapply impl_mono; [exact H|]. intros [|a] ms'; cbn; auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ebind_ret_ok : forall {A B} (a : A) (f : A -> itree (exc B)), ebind (Ret (Ok a)) f = f a.
Proof. reflexivity. Qed.
#[using="Type"] Lemma ebind_ret_unr : forall {A B} (f : A -> itree (exc B)), ebind (Ret Unr) f = Ret Unr.
Proof. reflexivity. Qed.
#[using="Type"] Lemma ebind_vis : forall {A B} n k (f : A -> itree (exc B)),
  ebind (Vis n k) f = Vis n (fun rsp => ebind (k rsp) f).
Proof. reflexivity. Qed.

#[using="Type"] Lemma impl_ret_ok : forall {A} (Q : A -> machine_state -> Prop) a ms,
  evt segs (Q a) ms -> impl (Ret (Ok a)) (epost Q) ms.
Proof. intros A Q a ms H. exact H. Qed.

(* [comment removed for export] *)
Definition enode {A} (n : node) (pl : resp -> option A) : itree (exc A) :=
  Vis n (fun rsp => match pl rsp with Some a => Ret (Ok a) | None => Ret Unr end).

#[using="Type"] Lemma impl_enode : forall {A} n (pl : resp -> option A) (Q : A -> machine_state -> Prop) ms,
  evt segs (fun ms1 => at_node n ms1 /\ forall rsp a, pl rsp = Some a -> evt segs (Q a) (nret ms1 rsp)) ms ->
  impl (enode n pl) (epost Q) ms.
Proof.
  intros A n pl Q ms H. apply impl_vis. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn.
  - apply Hk. reflexivity.
  - apply evt_done. exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma impl_enode_peek : forall {A} n f (pl : resp -> option A) (Q : A -> machine_state -> Prop) ms,
  npeek n = Some f ->
  evt segs (fun ms1 => forall a, pl (f ms1) = Some a -> evt segs (Q a) ms1) ms ->
  impl (enode n pl) (epost Q) ms.
Proof.
  intros A n f pl Q ms Hn H. apply (impl_peek n f _ _ ms Hn). eapply evt_mono; [exact H|]. intros ms1 Hk.
  cbn beta in *. destruct (pl (f ms1)) as [a|] eqn:E; cbn.
  - apply Hk. reflexivity.
  - apply evt_done. exact I.
Qed.

#[using="Type"] Lemma impl_enode_peek_now : forall {A} n f (pl : resp -> option A) (Q : A -> machine_state -> Prop) ms a,
  npeek n = Some f -> pl (f ms) = Some a -> evt segs (Q a) ms ->
  impl (enode n pl) (epost Q) ms.
Proof.
  intros A n f pl Q ms a Hn Hpl H. apply (impl_enode_peek n f pl Q ms Hn). apply evt_done.
  intros a' E. rewrite Hpl in E. injection E as <-. exact H.
Qed.

#[using="Type"] Lemma tpath_enode : forall {A} n (pl : resp -> option A) mo tr r mo',
  tpath (enode n pl) mo tr r mo' <->
  exists rsp, nstep n mo rsp mo' tr /\ r = match pl rsp with Some a => Ok a | None => Unr end.
Proof.
  intros A n pl mo tr r mo'. cbn. split.
  - intros (rsp & mo1 & evs & tr' & Hst & Hp & ->). exists rsp.
    destruct (pl rsp) as [a|]; cbn in Hp; destruct Hp as (<- & -> & ->); rewrite app_nil_r; split; auto.
  - intros (rsp & Hst & ->). exists rsp, mo', tr, []. split; [exact Hst|]. split; [|symmetry; apply app_nil_r].
    destruct (pl rsp); cbn; repeat split; reflexivity.
Qed.

#[using="Type"] Lemma texit_enode : forall {A} n (pl : resp -> option A) mo tr,
  texit (enode n pl) mo tr <-> exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')].
Proof.
  intros A n pl mo tr. cbn. split.
  - intros [H|(rsp & mo' & evs & tr' & _ & Hx & _)]; [exact H|]. destruct (pl rsp); destruct Hx.
  - intros H. left. exact H.
Qed.

#[using="Type"] Lemma tsafe_enode : forall {A} n (pl : resp -> option A) mo,
  tsafe (enode n pl) mo <-> nsafe n mo.
Proof.
  intros A n pl mo. cbn. split; [intros [H _]; exact H|]. intros H. split; [exact H|].
  intros rsp mo' evs _. destruct (pl rsp); exact I.
Qed.

#[using="Type"] Lemma tpath_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo tr r mo',
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

#[using="Type"] Lemma texit_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo tr,
  texit (ebind t f) mo tr <->
  texit t mo tr \/ exists tr1 a mo1 tr2, tpath t mo tr1 (Ok a) mo1 /\ texit (f a) mo1 tr2 /\ tr = tr1 ++ tr2.
Proof.
  intros A B t f mo tr. unfold ebind. rewrite texit_bind. split.
  - intros [H|(tr1 & [|a] & mo1 & tr2 & H1 & H2 & ->)]; [left; exact H| destruct H2 |].
    right. exists tr1, a, mo1, tr2. repeat split; assumption.
  - intros [H|(tr1 & a & mo1 & tr2 & H1 & H2 & ->)]; [left; exact H|].
    right. exists tr1, (Ok a), mo1, tr2. repeat split; assumption.
Qed.

#[using="Type"] Lemma ttrace_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo tr,
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

#[using="Type"] Lemma tsafe_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo,
  tsafe (ebind t f) mo <->
  tsafe t mo /\ (forall tr a mo', tpath t mo tr (Ok a) mo' -> tsafe (f a) mo').
Proof.
  intros A B t f mo. unfold ebind. rewrite tsafe_bind. split.
  - intros [Ht Hf]. split; [exact Ht|]. intros tr a mo' Hp. exact (Hf tr (Ok a) mo' Hp).
  - intros [Ht Hf]. split; [exact Ht|]. intros tr [|a] mo' Hp; [exact I|]. exact (Hf tr a mo' Hp).
Qed.

#[using="Type"] Lemma leaves_unreachable_m_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo,
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

(* [comment removed for export] *)

#[using="Type"] Lemma wreach_enode : forall {A} n (pl : resp -> option A) mo (P : list event -> exc A -> Model -> Prop) rsp mo' evs,
  npeek n = None -> nstep n mo rsp mo' evs ->
  P evs (match pl rsp with Some a => Ok a | None => Unr end) mo' ->
  wreach (enode n pl) mo P.
Proof.
  intros A n pl mo P rsp mo' evs Hn Hst HP. unfold enode. eapply wreach_vis; [exact Hn|exact Hst|].
  destruct (pl rsp) as [a|]; apply wreach_ret; rewrite app_nil_r; exact HP.
Qed.

#[using="Type"] Lemma wreach_enode_peek : forall {A} n f (pl : resp -> option A) mo (P : list event -> exc A -> Model -> Prop),
  npeek n = Some f ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> P evs (match pl rsp with Some a => Ok a | None => Unr end) mo') ->
  wreach (enode n pl) mo P.
Proof.
  intros A n f pl mo P Hn HP. unfold enode. eapply wreach_peek; [exact Hn|]. intros rsp mo' evs Hst.
  specialize (HP rsp mo' evs Hst). destruct (pl rsp) as [a|]; apply wreach_ret; rewrite app_nil_r; exact HP.
Qed.

#[using="Type"] Lemma wexit_enode : forall {A} n (pl : resp -> option A) mo (T : list event -> Prop) code mo',
  npeek n = None -> nexit n mo code mo' -> T [ExitEv code (m_fs mo')] -> wexit (enode n pl) mo T.
Proof. intros A n pl mo T code mo' Hn Hex HT. unfold enode. eapply wexit_exit; eassumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wreach_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo (P : list event -> exc B -> Model -> Prop),
  wreach t mo (fun tr1 r mo1 => match r with
                               | Ok a => wreach (f a) mo1 (fun tr2 => P (tr1 ++ tr2))
                               | Unr => P tr1 Unr mo1
                               end) ->
  wreach (ebind t f) mo P.
Proof.
  intros A B t f mo P H. unfold ebind. apply wreach_bind. eapply wreach_mono; [exact H|].
  intros tr1 [|a] mo1 H1; cbn beta in *; [|exact H1]. apply wreach_ret. rewrite app_nil_r. exact H1.
Qed.

#[using="Type"] Lemma wexit_ebind_l : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo T,
  wexit t mo T -> wexit (ebind t f) mo T.
Proof. intros A B t f mo T H. unfold ebind. apply wexit_bind_l. exact H. Qed.

#[using="Type"] Lemma wexit_ebind_r : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo (T : list event -> Prop),
  wreach t mo (fun tr1 r mo1 => exists a, r = Ok a /\ wexit (f a) mo1 (fun tr2 => T (tr1 ++ tr2))) ->
  wexit (ebind t f) mo T.
Proof.
  intros A B t f mo T H. unfold ebind. apply wexit_bind_r. eapply wreach_mono; [exact H|].
  intros tr1 r mo1 (a & -> & H1). exact H1.
Qed.

#[using="Type"] Lemma wins_ebind_l : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo T,
  wins t mo T -> wins (ebind t f) mo T.
Proof. intros A B t f mo T H. unfold ebind. apply wins_bind_l. exact H. Qed.

#[using="Type"] Lemma wins_ebind_r : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo (T : list event -> Prop),
  wreach t mo (fun tr1 r mo1 => exists a, r = Ok a /\ wins (f a) mo1 (fun tr2 => T (tr1 ++ tr2))) ->
  wins (ebind t f) mo T.
Proof.
  intros A B t f mo T H. unfold ebind. apply wins_bind_r. eapply wreach_mono; [exact H|].
  intros tr1 r mo1 (a & -> & H1). exact H1.
Qed.

#[using="Type"] Lemma npfree_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)),
  npfree t -> (forall a, npfree (f a)) -> npfree (ebind t f).
Proof. intros A B t f Ht Hf. unfold ebind. apply npfree_bind; [exact Ht|]. intros [|a]; [exact I|apply Hf]. Qed.

#[using="Type"] Lemma npfree_enode : forall {A} n (pl : resp -> option A), npeek n = None -> npfree (enode n pl).
Proof. intros A n pl Hn. cbn. split; [exact Hn|]. intros rsp. destruct (pl rsp); exact I. Qed.

End ITree.

Arguments Ret {node R} r.
Arguments Vis {node R} n k.
Arguments impl {node} segs at_node npeek {R} t Q ms.
Arguments ttrace {node} nstep nexit {R} t mo tr.
Arguments tsafe {node} nstep nsafe {R} t mo.
Arguments tpath {node} nstep {R} t mo tr r mo'.
Arguments texit {node} nstep nexit {R} t mo tr.
Arguments leaves_unreachable_m {node} nstep {R} t mo.
Arguments tree_at {node} segs at_node npeek nstep minv nsafe {R} t Q ms mo.
Arguments wreach {node} npeek nstep {R} t mo P.
Arguments wexit {node} npeek nstep nexit {R} t mo T.
Arguments wins {node} npeek nstep nexit {R} t mo T.
Arguments npfree {node} npeek {R} t.
Arguments peels {node} nstep {R} mo t t'.
Arguments ebind {node A B} t f.
Arguments enode {node A} n pl.
