(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Set Implicit Arguments.

(* [comment removed for export] *)
Definition model_idle (md : Model) : Prop :=
  m_halted md = None /\ m_vm_lazy md = [].

Lemma model_idle_halted : forall md, model_idle md -> m_halted md = None.
Proof. intros md [H _]; exact H. Qed.

Lemma model_idle_lazy : forall md, model_idle md -> m_vm_lazy md = [].
Proof. intros md [_ H]; exact H. Qed.

(* [comment removed for export] *)
Lemma model_idle_killed : forall md, model_idle md -> m_killed md = None.
Proof. intros md [H _]. apply m_killed_of_m_halted_none. exact H. Qed.

Section WithImage.

Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition world : Type := (list event * config)%type.

Definition w_tr (w : world) : list event := fst w.
Definition w_cfg (w : world) : config := snd w.

(* [comment removed for export] *)
Definition wstep (w w' : world) : Prop :=
  exists evs, sstep_a segs (w_cfg w) evs (SNext (w_cfg w'))
              /\ w_tr w' = w_tr w ++ evs.

Inductive wsteps : world -> world -> Prop :=
| wsteps_refl : forall w, wsteps w w
| wsteps_step : forall w1 w2 w3, wstep w1 w2 -> wsteps w2 w3 -> wsteps w1 w3.

Lemma wsteps_one : forall w w', wstep w w' -> wsteps w w'.
Proof using . intros; econstructor; eauto using wsteps_refl. Qed.

Lemma wsteps_trans : forall w1 w2 w3,
  wsteps w1 w2 -> wsteps w2 w3 -> wsteps w1 w3.
Proof using . induction 1; intros; eauto using wsteps_step. Qed.

(* [comment removed for export] *)
Lemma wsteps_star : forall w w',
  wsteps w w' -> exists tr, star_a segs (w_cfg w) tr (w_cfg w') /\ w_tr w' = w_tr w ++ tr.
Proof using .
  induction 1 as [w | w1 w2 w3 (evs & Hs & Ht) H23 IH].
  - exists []. split; [apply star_cfg_refl | now rewrite app_nil_r].
  - destruct IH as (tr & Hst & Htr). exists (evs ++ tr). split.
    + eapply star_cfg_step; eauto.
    + rewrite Htr, Ht, app_assoc. reflexivity.
Qed.

Lemma star_wsteps : forall c tr c' tr0,
  star_a segs c tr c' -> wsteps (tr0, c) (tr0 ++ tr, c').
Proof using .
  intros c tr c' tr0 H. revert tr0. unfold star_a in H.
  induction H as [c | c1 evs c2 tr c3 Hs Hst IH]; intros tr0.
  - rewrite app_nil_r. apply wsteps_refl.
  - eapply wsteps_step with (w2 := (tr0 ++ evs, c2)).
    + exists evs. split; [exact Hs | reflexivity].
    + rewrite app_assoc. apply IH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Safe.
Variable ok : world -> Prop.

Fixpoint safe (n : nat) (w : world) : Prop :=
  match n with
  | O => True
  | S n' => ok w /\ forall w', wstep w w' -> safe n' w'
  end.

Lemma safe_mono : forall n m w, (m <= n)%nat -> safe n w -> safe m w.
Proof using .
  induction n as [|n IH]; intros m w Hle Hs.
  - assert (m = 0%nat) by lia. subst. exact I.
  - destruct m as [|m]; [exact I|]. cbn in *. destruct Hs as [Hok Hk].
    split; [exact Hok|]. intros w' Hw. apply IH; [lia | auto].
Qed.

Lemma safe_S_ok : forall n w, safe (S n) w -> ok w.
Proof using . intros n w [H _]; exact H. Qed.

(* [comment removed for export] *)
Lemma safe_wsteps : forall w w',
  (forall n, safe n w) -> wsteps w w' -> forall n, safe n w'.
Proof using .
  intros w w' Hs Hst. induction Hst as [w | w1 w2 w3 Hw H23 IH]; [exact Hs|].
  apply IH. intros n. pose proof (Hs (S n)) as [_ Hk]. apply Hk, Hw.
Qed.

Lemma safe_reachable_ok : forall w w',
  (forall n, safe n w) -> wsteps w w' -> ok w'.
Proof using . intros w w' Hs Hst. exact (safe_S_ok (safe_wsteps Hs Hst 1)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition assn := world -> Prop.

Definition guards (n : nat) (Q : assn) : Prop := forall w, Q w -> safe n w.

Lemma guards_mono : forall n m Q, (m <= n)%nat -> guards n Q -> guards m Q.
Proof using . intros n m Q Hle Hg w Hq. eapply safe_mono; eauto. Qed.

Lemma guards_weaken : forall n (Q Q' : assn),
  (forall w, Q' w -> Q w) -> guards n Q -> guards n Q'.
Proof using . intros n Q Q' Himp Hg w Hq. apply Hg, Himp, Hq. Qed.

(* [comment removed for export] *)
Definition triple (P Q : assn) : Prop := forall n, guards n Q -> guards n P.
Definition triple1 (P Q : assn) : Prop := forall n, guards n Q -> guards (S n) P.

Lemma triple1_triple : forall P Q, triple1 P Q -> triple P Q.
Proof using .
  intros P Q H n Hg. eapply guards_mono with (n := S n); [lia|]. apply H, Hg.
Qed.

Lemma triple_refl : forall P, triple P P.
Proof using . intros P n Hg; exact Hg. Qed.

Lemma triple_conseq : forall (P P' Q Q' : assn),
  (forall w, P' w -> P w) -> (forall w, Q w -> Q' w) ->
  triple P Q -> triple P' Q'.
Proof using .
  intros P P' Q Q' HP HQ HT n Hg. eapply guards_weaken; [exact HP|].
  apply HT. eapply guards_weaken; [exact HQ|]. exact Hg.
Qed.

Lemma triple1_conseq : forall (P P' Q Q' : assn),
  (forall w, P' w -> P w) -> (forall w, Q w -> Q' w) ->
  triple1 P Q -> triple1 P' Q'.
Proof using .
  intros P P' Q Q' HP HQ HT n Hg. eapply guards_weaken; [exact HP|].
  apply HT. eapply guards_weaken; [exact HQ|]. exact Hg.
Qed.

Lemma triple_seq : forall P R Q, triple P R -> triple R Q -> triple P Q.
Proof using . intros P R Q H1 H2 n Hg. apply H1, H2, Hg. Qed.

Lemma triple1_seq_l : forall P R Q, triple1 P R -> triple R Q -> triple1 P Q.
Proof using . intros P R Q H1 H2 n Hg. apply H1, H2, Hg. Qed.

Lemma triple1_seq_r : forall P R Q, triple P R -> triple1 R Q -> triple1 P Q.
Proof using .
  intros P R Q H1 H2 n Hg. pose proof (H2 n Hg) as HgR.
  (* [comment removed for export] *)
  apply (H1 (S n)). exact HgR.
Qed.

(* [comment removed for export] *)
Lemma triple_disj : forall (P1 P2 Q : assn),
  triple P1 Q -> triple P2 Q -> triple (fun w => P1 w \/ P2 w) Q.
Proof using . intros P1 P2 Q H1 H2 n Hg w [Hp|Hp]; [apply H1 | apply H2]; auto. Qed.

Lemma triple_ex : forall (A : Type) (P : A -> assn) (Q : assn),
  (forall a, triple (P a) Q) -> triple (fun w => exists a, P a w) Q.
Proof using . intros A P Q H n Hg w [a Hp]. eapply H; eauto. Qed.

Lemma triple_pure : forall (X : Prop) (P Q : assn),
  (X -> triple P Q) -> triple (fun w => X /\ P w) Q.
Proof using . intros X P Q H n Hg w [Hx Hp]. eapply H; eauto. Qed.

Lemma triple1_disj : forall (P1 P2 Q : assn),
  triple1 P1 Q -> triple1 P2 Q -> triple1 (fun w => P1 w \/ P2 w) Q.
Proof using . intros P1 P2 Q H1 H2 n Hg w [Hp|Hp]; [apply H1 | apply H2]; auto. Qed.

Lemma triple1_ex : forall (A : Type) (P : A -> assn) (Q : assn),
  (forall a, triple1 (P a) Q) -> triple1 (fun w => exists a, P a w) Q.
Proof using . intros A P Q H n Hg w [a Hp]. eapply H; eauto. Qed.

Lemma triple1_pure : forall (X : Prop) (P Q : assn),
  (X -> triple1 P Q) -> triple1 (fun w => X /\ P w) Q.
Proof using . intros X P Q H n Hg w [Hx Hp]. eapply H; eauto. Qed.

(* [comment removed for export] *)
Lemma triple_post_l : forall (P Q1 Q2 : assn),
  triple P Q1 -> triple P (fun w => Q1 w \/ Q2 w).
Proof using . intros. eapply triple_conseq; [ | | eassumption]; cbn; auto. Qed.

Lemma triple_post_r : forall (P Q1 Q2 : assn),
  triple P Q2 -> triple P (fun w => Q1 w \/ Q2 w).
Proof using . intros. eapply triple_conseq; [ | | eassumption]; cbn; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma triple1_step : forall (P Q : assn),
  (forall w, P w -> ok w /\ forall w', wstep w w' -> Q w') ->
  triple1 P Q.
Proof using .
  intros P Q H n Hg w Hp. cbn. destruct (H w Hp) as [Hok Hsucc].
  split; [exact Hok|]. intros w' Hw. apply Hg, Hsucc, Hw.
Qed.

(* [comment removed for export] *)
Lemma triple_halt : forall (P : assn),
  (forall w, P w -> ok w /\ forall w', ~ wstep w w') ->
  triple P (fun _ => False).
Proof using .
  intros P H. apply triple1_triple. apply triple1_step.
  intros w Hp. destruct (H w Hp) as [Hok Hn]. split; [exact Hok|].
  intros w' Hw. exfalso. exact (Hn w' Hw).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma triple_loop : forall (Inv Q : assn),
  triple1 Inv (fun w => Inv w \/ Q w) -> triple Inv Q.
Proof using .
  intros Inv Q Hbody n. induction n as [|n IH]; intros Hg.
  - intros w _. exact Logic.I.
  - apply Hbody. intros w [Hi | Hq].
    + apply IH; [|exact Hi]. eapply guards_mono; [|exact Hg]. lia.
    + eapply safe_mono; [|exact (Hg w Hq)]. lia.
Qed.

(* [comment removed for export] *)
Definition tripleN (n : nat) (P Q : assn) : Prop := guards n Q -> guards n P.

Lemma triple_of_tripleN : forall P Q, (forall n, tripleN n P Q) -> triple P Q.
Proof using . intros P Q H n. apply H. Qed.

Lemma lob : forall (A : Type) (P Q : A -> assn),
  (forall n, (forall a m, (m < n)%nat -> tripleN m (P a) (Q a)) ->
             forall a, tripleN n (P a) (Q a)) ->
  forall a, triple (P a) (Q a).
Proof using .
  intros A P Q H a n. revert a.
  induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf).
  apply H. intros a m Hm. exact (IH m Hm a).
Qed.

(* [comment removed for export] *)
Lemma tripleN_seq : forall n P R Q, tripleN n P R -> tripleN n R Q -> tripleN n P Q.
Proof using . intros n P R Q H1 H2 Hg. apply H1, H2, Hg. Qed.

Lemma tripleN_of_triple : forall n P Q, triple P Q -> tripleN n P Q.
Proof using . intros n P Q H. exact (H n). Qed.

(* [comment removed for export] *)
Lemma tripleN_step_later : forall n (P R Q : assn),
  (forall w, P w -> ok w /\ forall w', wstep w w' -> R w') ->
  (forall m, (m < n)%nat -> tripleN m R Q) ->
  tripleN n P Q.
Proof using .
  intros n P R Q Hstep Hlater Hg w Hp. destruct n as [|n]; [exact I|].
  cbn. destruct (Hstep w Hp) as [Hok Hsucc]. split; [exact Hok|].
  intros w' Hw. apply (Hlater n); [lia| |apply Hsucc, Hw].
  eapply guards_mono; [|exact Hg]. lia.
Qed.

End Safe.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition etriple (P Q : world -> Prop) : Prop :=
  forall w, P w -> exists w', wsteps w w' /\ Q w'.

Lemma etriple_refl : forall P, etriple P P.
Proof using . intros P w Hp. exists w. split; [apply wsteps_refl | exact Hp]. Qed.

Lemma etriple_seq : forall P R Q, etriple P R -> etriple R Q -> etriple P Q.
Proof using .
  intros P R Q H1 H2 w Hp. destruct (H1 w Hp) as (w1 & Hs1 & Hr).
  destruct (H2 w1 Hr) as (w2 & Hs2 & Hq). exists w2.
  split; [eapply wsteps_trans; eauto | exact Hq].
Qed.

Lemma etriple_conseq : forall (P P' Q Q' : world -> Prop),
  (forall w, P' w -> P w) -> (forall w, Q w -> Q' w) ->
  etriple P Q -> etriple P' Q'.
Proof using .
  intros P P' Q Q' HP HQ H w Hp. destruct (H w (HP w Hp)) as (w' & Hs & Hq).
  exists w'. split; [exact Hs | apply HQ, Hq].
Qed.

Lemma etriple_step : forall (P Q : world -> Prop),
  (forall w, P w -> exists w', wstep w w' /\ Q w') -> etriple P Q.
Proof using .
  intros P Q H w Hp. destruct (H w Hp) as (w' & Hs & Hq).
  exists w'. split; [apply wsteps_one, Hs | exact Hq].
Qed.

Lemma etriple_ex : forall (A : Type) (P : A -> world -> Prop) Q,
  (forall a, etriple (P a) Q) -> etriple (fun w => exists a, P a w) Q.
Proof using . intros A P Q H w [a Hp]. eapply H; eauto. Qed.

Lemma etriple_disj : forall (P1 P2 Q : world -> Prop),
  etriple P1 Q -> etriple P2 Q -> etriple (fun w => P1 w \/ P2 w) Q.
Proof using . intros P1 P2 Q H1 H2 w [H|H]; [apply H1 | apply H2]; auto. Qed.

Lemma etriple_pure : forall (X : Prop) (P Q : world -> Prop),
  (X -> etriple P Q) -> etriple (fun w => X /\ P w) Q.
Proof using . intros X P Q H w [Hx Hp]. eapply H; eauto. Qed.

(* [comment removed for export] *)
Lemma etriple_loop : forall (A : Type) (R : A -> A -> Prop) (wfR : well_founded R)
    (I : A -> world -> Prop) (Q : world -> Prop),
  (forall a, etriple (I a) (fun w => (exists a', R a' a /\ I a' w) \/ Q w)) ->
  forall a, etriple (I a) Q.
Proof using .
  intros A R wfR I Q Hbody a.
  induction a as [a IH] using (well_founded_induction wfR).
  intros w Hi. destruct (Hbody a w Hi) as (w1 & Hs1 & [[a' [Hr Hi']] | Hq]).
  - destruct (IH a' Hr w1 Hi') as (w2 & Hs2 & Hq).
    exists w2. split; [eapply wsteps_trans; eauto | exact Hq].
  - exists w1. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Assembly.

(* [comment removed for export] *)
Variable c0 : config.
Variable Spec : list event -> Prop.

Definition w0 : world := ([], c0).

(* [comment removed for export] *)
Definition tcons (tr : list event) : Prop := exists t, Spec t /\ is_prefix tr t.

Definition ok_src (w : world) : Prop :=
  tcons (w_tr w) /\ ~ unmodeled_at segs (w_cfg w).

Definition ok_tgt (w : world) : Prop :=
  tcons (w_tr w) /\ forall evs, ~ sstep segs (w_cfg w) evs SError.

Definition SOUND : Prop :=
  forall tr c, star_a segs c0 tr c -> tcons tr.
Definition COMPLETE : Prop :=
  forall t, Spec t -> exists c, star_a segs c0 t c.

Lemma safe_src_sound : (forall n, safe ok_src n w0) -> SOUND.
Proof using .
  intros Hs tr c Hst.
  pose proof (@safe_reachable_ok ok_src w0 (tr, c) Hs) as H.
  assert (Hw : wsteps w0 ([] ++ tr, c)) by (apply star_wsteps; exact Hst).
  cbn in Hw. destruct (H Hw) as [Ht _]. exact Ht.
Qed.

Lemma safe_src_modeled : (forall n, safe ok_src n w0) -> ~ reaches_unmodeled_a segs c0.
Proof using .
  intros Hs (tr & c & Hst & Hun).
  assert (Hw : wsteps w0 ([] ++ tr, c)) by (apply star_wsteps; exact Hst).
  destruct (@safe_reachable_ok ok_src w0 (tr, c) Hs Hw) as [_ Hn]. exact (Hn Hun).
Qed.

Lemma safe_tgt_sound : (forall n, safe ok_tgt n w0) -> SOUND.
Proof using .
  intros Hs tr c Hst.
  assert (Hw : wsteps w0 ([] ++ tr, c)) by (apply star_wsteps; exact Hst).
  destruct (@safe_reachable_ok ok_tgt w0 (tr, c) Hs Hw) as [Ht _]. exact Ht.
Qed.

Lemma safe_tgt_noerror : (forall n, safe ok_tgt n w0) -> ~ reaches_error_a segs c0.
Proof using .
  intros Hs (tr & c & evs & Hst & Herr).
  assert (Hw : wsteps w0 ([] ++ tr, c)) by (apply star_wsteps; exact Hst).
  destruct (@safe_reachable_ok ok_tgt w0 (tr, c) Hs Hw) as [_ Hn]. exact (Hn evs (sstep_cfg_sub _ _ _ _ _ Herr)).
Qed.

(* [comment removed for export] *)
Lemma triple_init_safe : forall ok (Init : assn),
  Init w0 -> triple ok Init (fun _ => False) -> forall n, safe ok n w0.
Proof using .
  intros ok Init Hi Ht n. apply (Ht n); [|exact Hi]. intros w Hf. destruct Hf.
Qed.

(* [comment removed for export] *)
Lemma etriple_complete :
  (forall t, Spec t -> etriple (fun w => w = w0) (fun w => w_tr w = t)) -> COMPLETE.
Proof using .
  intros H t Ht. destruct (H t Ht w0 eq_refl) as (w' & Hs & Htr).
  destruct (wsteps_star Hs) as (tr & Hst & Heq). cbn in *.
  exists (w_cfg w'). rewrite Htr in Heq. cbn in Heq. subst. exact Hst.
Qed.

(* [comment removed for export] *)
Lemma obs_trace_iff : SOUND -> COMPLETE ->
  forall tr, obs_trace_a segs c0 tr <-> tcons tr.
Proof using .
  intros Hs Hc tr. split.
  - intros (tr' & c & Hst & Hp). destruct (Hs _ _ Hst) as (t & Ht & Hp').
    exists t. split; [exact Ht | eapply is_prefix_trans; eauto].
  - intros (t & Ht & Hp). destruct (Hc t Ht) as (c & Hst).
    exists t, c. split; assumption.
Qed.

End Assembly.

End WithImage.

