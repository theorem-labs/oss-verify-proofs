(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import ShapeAlgBase.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section WithCfg.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_ok_cfg (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs cfg c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs cfg c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Inductive realizes_cfg : config -> TSet -> Prop :=
| rzc_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok_cfg c I evs nx ->
    (forall i, realizes_cfg (nx i) (T i)) ->
    realizes_cfg c (t_alt (fun i => t_emit (evs i) (T i)))
| rzc_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes_cfg c t_nil
| rzc_conseq : forall c T T',
    realizes_cfg c T -> t_eq T T' -> realizes_cfg c T'.

(* [comment removed for export] *)
Lemma rzc_eq : forall c (T T' : TSet),
  t_eq T T' -> realizes_cfg c T -> realizes_cfg c T'.
Proof. intros c T T' Heq H. eapply rzc_conseq; eassumption. Qed.

(* [comment removed for export] *)

Lemma realizes_cfg_nonempty : forall c T, realizes_cfg c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma realizes_cfg_pclosed : forall c T, realizes_cfg c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

Lemma realizes_cfg_pclosed' : forall c T, realizes_cfg c T -> pclosed T.
Proof. intros c T H tr tr'. apply (realizes_cfg_pclosed c T H). Qed.

(* [comment removed for export] *)

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs cfg c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs cfg c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
Qed.

Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs).
  eapply star_cfg_step; [exact H | apply star_cfg_refl].
Qed.

Lemma star_cfg_trans : forall c1 t1 c2 t2 c3,
  star_cfg segs cfg c1 t1 c2 -> star_cfg segs cfg c2 t2 c3 ->
  star_cfg segs cfg c1 (t1 ++ t2) c3.
Proof.
  intros c1 t1 c2 t2 c3 H1; revert t2 c3.
  induction H1 as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros t2 c3' H2; cbn; [assumption|].
  rewrite <- app_assoc. eapply star_cfg_step; [exact Hss | apply IH; exact H2].
Qed.

Lemma obs_trace_cfg_nil : forall c, obs_trace_cfg segs cfg c [].
Proof. intros c. exists [], c. split; [apply star_cfg_refl | exact I]. Qed.

Lemma realizes_cfg_star_only : forall c T, realizes_cfg c T ->
  forall tr c', star_cfg segs cfg c tr c' -> T tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil c tr c' Hh Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

Lemma realizes_cfg_complete : forall c T, realizes_cfg c T ->
  forall tr, T tr -> obs_trace_cfg segs cfg c tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar]
             | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
Theorem realizes_cfg_obs_iff : forall c T, realizes_cfg c T ->
  forall tr, obs_trace_cfg segs cfg c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_cfg_pclosed; [exact H | eapply realizes_cfg_star_only; eauto | exact Hp].
  - apply realizes_cfg_complete; exact H.
Qed.

(* [comment removed for export] *)
Corollary realizes_cfg_fun : forall c T T',
  realizes_cfg c T -> realizes_cfg c T' -> t_eq T T'.
Proof.
  intros c T T' H H' tr.
  rewrite <- (realizes_cfg_obs_iff c T H tr). apply realizes_cfg_obs_iff. exact H'.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma realizes_cfg_step : forall c T e c',
  realizes_cfg c T -> sstep_cfg segs cfg c e (SNext c') ->
  exists T', realizes_cfg c' T' /\ (forall tr, T' tr -> T (e ++ tr)).
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & -> & Heq2).
    inversion Heq2; subst c'. exists (T i). split; [apply Hcont |].
    intros tr Htr. exists i. right. exists tr. split; [reflexivity | exact Htr].
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - destruct (IH e c' Hss) as (T0 & Hrz & Hsub).
    exists T0. split; [exact Hrz | intros tr Htr; apply Heq, Hsub, Htr].
Qed.

Lemma realizes_cfg_star : forall c T tr c',
  realizes_cfg c T -> star_cfg segs cfg c tr c' ->
  exists T', realizes_cfg c' T' /\ (forall tr', T' tr' -> T (tr ++ tr')).
Proof.
  intros c T tr c' H Hstar. revert T H.
  induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros T H.
  - exists T. split; [exact H | intros tr' Htr'; exact Htr'].
  - destruct (realizes_cfg_step c1 T evs c2 H Hss) as (T1 & H1 & Hsub1).
    destruct (IH T1 H1) as (T2 & H2 & Hsub2).
    exists T2. split; [exact H2 |].
    intros tr' Htr'. rewrite <- app_assoc. apply Hsub1, Hsub2, Htr'.
Qed.

Lemma realizes_cfg_no_sserror : forall c T e,
  realizes_cfg c T -> ~ sstep_cfg segs cfg c e SError.
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Theorem realizes_cfg_no_error : forall c T,
  realizes_cfg c T -> ~ reaches_error_cfg segs cfg c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  destruct (realizes_cfg_star c T tr c' H Hstar) as (T' & H' & _).
  exact (realizes_cfg_no_sserror c' T' evs H' Herr).
Qed.

Corollary realizes_cfg_no_unmodeled : forall c T,
  realizes_cfg c T -> ~ reaches_unmodeled_cfg segs cfg c.
Proof.
  intros c T H Hun. apply (realizes_cfg_no_error c T H).
  apply reaches_unmodeled_cfg_reaches_error_cfg. exact Hun.
Qed.

Corollary realizes_cfg_not_all_error : forall c T,
  realizes_cfg c T -> ~ all_traces_error_cfg segs cfg c.
Proof.
  intros c T H Hall. apply (realizes_cfg_no_error c T H).
  apply all_traces_error_cfg_reaches_error_cfg. exact Hall.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rzc_silent1 : forall c c' T,
  node_ok_cfg c unit (fun _ => []) (fun _ => c') ->
  realizes_cfg c' T ->
  realizes_cfg c T.
Proof.
  intros c c' T Hnode Hc.
  apply (rzc_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzc_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_cfg_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
Lemma rzc_emit1 : forall c c' e T,
  node_ok_cfg c unit (fun _ => e) (fun _ => c') ->
  realizes_cfg c' T ->
  realizes_cfg c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (rzc_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rzc_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
Lemma rzc_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok_cfg c I (fun _ => []) nx ->
  (forall i, realizes_cfg (nx i) (T i)) ->
  realizes_cfg c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (rzc_conseq c (t_alt (fun i => t_emit [] (T i)))).
  - apply (rzc_node c I (fun _ => []) nx T i0 Hnode Hc).
  - apply t_alt_emit_nil. intros i. eapply realizes_cfg_nonempty. apply Hc.
Qed.

(* [comment removed for export] *)
Lemma rzc_cases_same : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok_cfg c I (fun _ => []) nx ->
  (forall i, realizes_cfg (nx i) T) ->
  realizes_cfg c T.
Proof.
  intros c I nx T i0 Hnode Hc.
  eapply rzc_conseq; [apply (rzc_cases c I nx (fun _ => T) i0 Hnode Hc) |].
  apply t_alt_const. exact i0.
Qed.

(* [comment removed for export] *)
Lemma rzc_emit_cases : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                              (T : I -> TSet) (i0 : I),
  node_ok_cfg c I evs nx ->
  (forall i, realizes_cfg (nx i) (T i)) ->
  realizes_cfg c (t_alt (fun i => t_emit (evs i) (T i))).
Proof. intros. eapply rzc_node; eassumption. Qed.

(* [comment removed for export] *)
Lemma rzc_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  node_ok_cfg c (IA + IB) (fun _ => []) nx ->
  (forall i, realizes_cfg (nx (inl i)) A) ->
  (forall i, realizes_cfg (nx (inr i)) B) ->
  realizes_cfg c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply realizes_cfg_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply realizes_cfg_nonempty; apply (HB b0)).
  apply (rzc_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (rzc_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)
Inductive det_path_cfg : config -> list event -> config -> Prop :=
| dpc_refl : forall c, det_path_cfg c [] c
| dpc_step : forall c e c1 tr c2,
    node_ok_cfg c unit (fun _ => e) (fun _ => c1) ->
    det_path_cfg c1 tr c2 ->
    det_path_cfg c (e ++ tr) c2.

Lemma det_path_cfg_one : forall c e c',
  node_ok_cfg c unit (fun _ => e) (fun _ => c') -> det_path_cfg c e c'.
Proof.
  intros c e c' H. rewrite <- (app_nil_r e). eapply dpc_step; [exact H | apply dpc_refl].
Qed.

Lemma det_path_cfg_trans : forall c1 t1 c2 t2 c3,
  det_path_cfg c1 t1 c2 -> det_path_cfg c2 t2 c3 -> det_path_cfg c1 (t1 ++ t2) c3.
Proof.
  intros c1 t1 c2 t2 c3 H1; revert t2 c3.
  induction H1 as [c | c e c1' tr c2' Hn Hp IH]; intros t2 c3 H2; cbn; [assumption|].
  rewrite <- app_assoc. eapply dpc_step; [exact Hn | apply IH; exact H2].
Qed.

Lemma det_path_cfg_star : forall c tr c',
  det_path_cfg c tr c' -> star_cfg segs cfg c tr c'.
Proof.
  intros c tr c' H. induction H as [c | c e c1 tr c2 [Hcomp _] Hp IH].
  - apply star_cfg_refl.
  - eapply star_cfg_step; [exact (Hcomp tt) | exact IH].
Qed.

(* [comment removed for export] *)
Lemma rzc_det_path : forall c tr c' T,
  det_path_cfg c tr c' ->
  realizes_cfg c' T ->
  realizes_cfg c (t_emit tr T).
Proof.
  intros c tr c' T Hp. revert T.
  induction Hp as [c | c e c1 tr c2 Hn Hp IH]; intros T Hc.
  - eapply rzc_conseq; [exact Hc |].
    apply t_eq_sym, t_emit_nil_eq. eapply realizes_cfg_nonempty; exact Hc.
  - eapply rzc_conseq; [eapply rzc_emit1; [exact Hn | apply IH; exact Hc] |].
    apply t_eq_sym, t_emit_app.
Qed.

Lemma rzc_det_path_silent : forall c c' T,
  det_path_cfg c [] c' ->
  realizes_cfg c' T ->
  realizes_cfg c T.
Proof.
  intros c c' T Hp Hc.
  eapply rzc_conseq; [eapply rzc_det_path; eassumption |].
  apply t_emit_nil_eq. eapply realizes_cfg_nonempty; exact Hc.
Qed.

(* [comment removed for export] *)

Definition within_budget_cfg (c : config) : Prop :=
  ~ reaches_budget_refused_cfg segs cfg c.

Lemma within_budget_cfg_here : forall c,
  within_budget_cfg c -> ~ budget_refused_at segs c.
Proof.
  intros c H Hb. apply H. exists [], c. split; [apply star_cfg_refl | exact Hb].
Qed.

Lemma within_budget_cfg_star : forall c tr c',
  within_budget_cfg c -> star_cfg segs cfg c tr c' -> within_budget_cfg c'.
Proof.
  intros c tr c' H Hstar (tr' & c'' & Hstar' & Hb).
  apply H. exists (tr ++ tr'), c''. split; [| exact Hb].
  eapply star_cfg_trans; eassumption.
Qed.

Lemma within_budget_cfg_step : forall c e c',
  within_budget_cfg c -> sstep_cfg segs cfg c e (SNext c') -> within_budget_cfg c'.
Proof.
  intros c e c' H Hss. eapply within_budget_cfg_star; [exact H | apply star_cfg_one; exact Hss].
Qed.

Lemma within_budget_cfg_det_path : forall c tr c',
  within_budget_cfg c -> det_path_cfg c tr c' -> within_budget_cfg c'.
Proof.
  intros c tr c' H Hp. eapply within_budget_cfg_star; [exact H | apply det_path_cfg_star; exact Hp].
Qed.

(* [comment removed for export] *)
Lemma rzc_node_wb : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                           (T : I -> TSet) (i0 : I),
  within_budget_cfg c ->
  (~ budget_refused_at segs c -> node_ok_cfg c I evs nx) ->
  (forall i, within_budget_cfg (nx i) -> realizes_cfg (nx i) (T i)) ->
  realizes_cfg c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 Hwb Hnode Hcont.
  pose proof (Hnode (within_budget_cfg_here c Hwb)) as Hn.
  apply (rzc_node c I evs nx T i0 Hn).
  intros i. apply Hcont. eapply within_budget_cfg_step; [exact Hwb | apply (proj1 Hn i)].
Qed.

(* [comment removed for export] *)

Definition ev_exits_with (code : word) (e : event) : Prop :=
  match e with
  | ExitEv c _ => c = code
  | KillEv _ _ => False
  | _ => True
  end.

(* [comment removed for export] *)
Definition exits_only (code : word) (T : TSet) : Prop :=
  forall tr, T tr -> Forall (ev_exits_with code) tr.

Lemma exits_only_nil : forall code, exits_only code t_nil.
Proof. intros code tr ->. constructor. Qed.

Lemma is_prefix_Forall {A} (P : A -> Prop) : forall (l1 l2 : list A),
  is_prefix l1 l2 -> Forall P l2 -> Forall P l1.
Proof.
  induction l1 as [|x l1 IH]; intros l2 Hp HF; [constructor|].
  destruct l2 as [|y l2]; cbn in Hp; [contradiction|].
  destruct Hp as [-> Hp]. inversion HF; subst. constructor; [assumption | eapply IH; eauto].
Qed.

Lemma exits_only_emit : forall code e T,
  Forall (ev_exits_with code) e -> exits_only code T -> exits_only code (t_emit e T).
Proof.
  intros code e T He HT tr [Hp | (tr' & -> & Htr')].
  - eapply is_prefix_Forall; eassumption.
  - apply Forall_app. split; [exact He | apply HT; exact Htr'].
Qed.

Lemma exits_only_exit : forall code fs, exits_only code (t_exit code fs).
Proof.
  intros code fs. apply exits_only_emit; [| apply exits_only_nil].
  constructor; [reflexivity | constructor].
Qed.

Lemma Forall_exits_with_writes : forall code ch (l : list byte),
  Forall (ev_exits_with code) (map (WriteEv ch) l).
Proof. intros code ch l. induction l; cbn; constructor; [exact I | assumption]. Qed.

Lemma Forall_exits_with_reads : forall code ch (l : list byte),
  Forall (ev_exits_with code) (map (ReadEv ch) l).
Proof. intros code ch l. induction l; cbn; constructor; [exact I | assumption]. Qed.

Lemma exits_only_alt : forall code (I : Type) (f : I -> TSet),
  (forall i, exits_only code (f i)) -> exits_only code (t_alt f).
Proof. intros code I f H tr [i Hi]. exact (H i tr Hi). Qed.

Lemma exits_only_alt2 : forall code A B,
  exits_only code A -> exits_only code B -> exits_only code (t_alt2 A B).
Proof. intros code A B HA HB tr [H | H]; [apply HA | apply HB]; exact H. Qed.

Lemma exits_only_t_eq : forall code T T',
  t_eq T T' -> exits_only code T -> exits_only code T'.
Proof. intros code T T' Heq H tr Htr. apply H, Heq, Htr. Qed.

(* [comment removed for export] *)
Theorem realizes_cfg_must_exit : forall code c T,
  realizes_cfg c T ->
  m_halted (cfg_model c) = None ->
  exits_only code T ->
  must_exit_at_cfg cfg segs code c.
Proof.
  intros code c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros Hrun Hex.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_at_cfg_running.
    + exact Hrun.
    + exists (evs i0), (SNext (nx i0)). apply Hcomp.
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Hbad). discriminate Hbad.
    + intros e c' Hss.
      destruct (Hsound e (SNext c') Hss) as (i & -> & Heq2).
      inversion Heq2; subst c'. clear Heq2.
      assert (Hevs : Forall (ev_exits_with code) (evs i)).
      { apply Hex. exists i. left. apply is_prefix_refl. }
      destruct (m_halted (cfg_model (nx i))) as [code' |] eqn:Hh'.
      * destruct (sstep_cfg_next_halts_by_exit segs cfg c (evs i) (nx i) Hss)
          as [Hnone | [(evs0 & code1 & Hev & Hh1 & Hk1) | (evs0 & sig & Hev & Hk1)]].
        { rewrite Hh' in Hnone. discriminate Hnone. }
        { rewrite Hev in Hevs. apply Forall_app in Hevs as [_ Hlast].
          inversion Hlast as [| ? ? Hc _]; subst. cbn in Hc. subst code1.
          apply must_exit_at_cfg_halted; assumption. }
        { exfalso. rewrite Hev in Hevs. apply Forall_app in Hevs as [_ Hlast].
          inversion Hlast as [| ? ? Hc _]; subst. exact Hc. }
      * apply (IH i Hh').
        intros tr Htr.
        assert (HF : Forall (ev_exits_with code) (evs i ++ tr)).
        { apply Hex. exists i. right. exists tr. split; [reflexivity | exact Htr]. }
        apply Forall_app in HF as [_ HF]. exact HF.
  - contradiction.
  - apply IH; [exact Hrun |]. eapply exits_only_t_eq; [apply t_eq_sym; exact Heq | exact Hex].
Qed.

End WithCfg.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition init_cfg (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) : config :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
      init_config segs pc ph sp brk0 mbase rnd lim inp
  end.

Lemma init_cfg_eq : forall segs pc ph sp brk0 mbase rnd lim inp,
  init_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mbase rnd) inp
  = init_config segs pc ph sp brk0 mbase rnd lim inp.
Proof. reflexivity. Qed.

Lemma init_cfg_not_halted : forall img lim en inp,
  m_halted (cfg_model (init_cfg img lim en inp)) = None.
Proof. intros [segs pc ph] lim [sp brk0 mbase rnd] inp. reflexivity. Qed.

Section RunLevel.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma realizes_cfg_run_traces_iff : forall img lim en inp T,
  realizes_cfg cfg (img_segments img) (init_cfg img lim en inp) T ->
  forall tr, bh_traces (run_scfg cfg img lim en inp) tr <-> T tr.
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp T H tr.
  cbn [run_scfg bh_traces]. apply realizes_cfg_obs_iff. exact H.
Qed.

Lemma realizes_cfg_run_error_free : forall img lim en inp T,
  realizes_cfg cfg (img_segments img) (init_cfg img lim en inp) T ->
  error_free (run_scfg cfg img lim en inp).
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp T H.
  unfold error_free. cbn [run_scfg bh_errors]. eapply realizes_cfg_no_error. exact H.
Qed.

Lemma realizes_cfg_run_modeled : forall img lim en inp T,
  realizes_cfg cfg (img_segments img) (init_cfg img lim en inp) T ->
  modeled (run_scfg cfg img lim en inp).
Proof.
  intros img lim en inp T H Hun.
  apply (realizes_cfg_run_error_free img lim en inp T H).
  apply run_scfg_unmodeled_errors. exact Hun.
Qed.

Lemma realizes_cfg_run_not_all_errors : forall img lim en inp T,
  realizes_cfg cfg (img_segments img) (init_cfg img lim en inp) T ->
  ~ bh_all_errors (run_scfg cfg img lim en inp).
Proof.
  intros img lim en inp T H Hall.
  apply (realizes_cfg_run_error_free img lim en inp T H).
  apply run_scfg_all_errors_errors. exact Hall.
Qed.

(* [comment removed for export] *)
Theorem shape_cfg_strong_equiv_ef_img :
  forall (lim_s lim_t : Z) (src tgt : Image) (en_s en_t : ExecEntry)
         (T : TSet) (inp : ProcInput),
  realizes_cfg cfg (img_segments src) (init_cfg src lim_s en_s inp) T ->
  realizes_cfg cfg (img_segments tgt) (init_cfg tgt lim_t en_t inp) T ->
  strong_equiv_error_free_budgets_scfg cfg lim_s lim_t src tgt en_s en_t inp.
Proof.
  intros lim_s lim_t src tgt en_s en_t T inp Hs Ht.
  split; [| split].
  - eapply realizes_cfg_run_error_free; exact Hs.
  - eapply realizes_cfg_run_error_free; exact Ht.
  - intro tr.
    rewrite (realizes_cfg_run_traces_iff src lim_s en_s inp T Hs tr).
    rewrite (realizes_cfg_run_traces_iff tgt lim_t en_t inp T Ht tr).
    reflexivity.
Qed.

(* [comment removed for export] *)
Corollary shape_cfg_strong_equiv_ef_img_eq :
  forall (lim_s lim_t : Z) (src tgt : Image) (en_s en_t : ExecEntry)
         (T T' : TSet) (inp : ProcInput),
  realizes_cfg cfg (img_segments src) (init_cfg src lim_s en_s inp) T ->
  realizes_cfg cfg (img_segments tgt) (init_cfg tgt lim_t en_t inp) T' ->
  t_eq T T' ->
  strong_equiv_error_free_budgets_scfg cfg lim_s lim_t src tgt en_s en_t inp.
Proof.
  intros lim_s lim_t src tgt en_s en_t T T' inp Hs Ht Heq.
  eapply shape_cfg_strong_equiv_ef_img; [| exact Ht].
  eapply rzc_conseq; [exact Hs | exact Heq].
Qed.

(* [comment removed for export] *)
Theorem shape_cfg_strong_equiv_ef :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes_cfg cfg source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes_cfg cfg target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv
       (bh_traces (run_scfg cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
       (bh_traces (run_scfg cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hs Ht.
  exact (shape_cfg_strong_equiv_ef_img rlim alim (mkImage source_segs rpc rph)
           (mkImage target_segs apc aph) (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd)
           T inp Hs Ht).
Qed.

Corollary shape_cfg_strong_equiv_ef_eq :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  realizes_cfg cfg source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes_cfg cfg target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  strong_equiv_error_free_budgets_scfg cfg rlim alim
    (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T T' inp Hs Ht Heq.
  exact (shape_cfg_strong_equiv_ef_img_eq rlim alim (mkImage source_segs rpc rph)
           (mkImage target_segs apc aph) (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd)
           T T' inp Hs Ht Heq).
Qed.

(* [comment removed for export] *)
Lemma source_within_budget_init : forall lim_s src en_s inp,
  source_within_budget_scfg cfg lim_s src en_s inp ->
  within_budget_cfg cfg (img_segments src) (init_cfg src lim_s en_s inp).
Proof.
  intros lim_s [segs pc ph] [sp brk0 mbase rnd] inp H. exact H.
Qed.

Lemma source_within_budget_init_iff : forall lim_s src en_s inp,
  source_within_budget_scfg cfg lim_s src en_s inp
  <-> within_budget_cfg cfg (img_segments src) (init_cfg src lim_s en_s inp).
Proof.
  intros lim_s [segs pc ph] [sp brk0 mbase rnd] inp. split; intros H; exact H.
Qed.

(* [comment removed for export] *)
Theorem shape_cfg_universal :
  forall (lim_s lim_t : Z) (src tgt : Image),
  (forall en_s en_t inp,
     valid_entry src en_s inp ->
     valid_entry tgt en_t inp ->
     valid_input inp ->
     source_within_budget_scfg cfg lim_s src en_s inp ->
     exists T : TSet,
       realizes_cfg cfg (img_segments src) (init_cfg src lim_s en_s inp) T
       /\ realizes_cfg cfg (img_segments tgt) (init_cfg tgt lim_t en_t inp) T) ->
  strong_universal_error_free_T_scfg_budgets cfg lim_s lim_t src tgt.
Proof.
  intros lim_s lim_t src tgt H en_s en_t inp Hvs Hvt Hvi Hb.
  destruct (H en_s en_t inp Hvs Hvt Hvi Hb) as (T & Hs & Ht).
  exact (shape_cfg_strong_equiv_ef_img lim_s lim_t src tgt en_s en_t T inp Hs Ht).
Qed.

(* [comment removed for export] *)
Theorem shape_cfg_universal_eq :
  forall (lim_s lim_t : Z) (src tgt : Image),
  (forall en_s en_t inp,
     valid_entry src en_s inp ->
     valid_entry tgt en_t inp ->
     valid_input inp ->
     source_within_budget_scfg cfg lim_s src en_s inp ->
     exists Ts Tt : TSet,
       realizes_cfg cfg (img_segments src) (init_cfg src lim_s en_s inp) Ts
       /\ realizes_cfg cfg (img_segments tgt) (init_cfg tgt lim_t en_t inp) Tt
       /\ t_eq Ts Tt) ->
  strong_universal_error_free_T_scfg_budgets cfg lim_s lim_t src tgt.
Proof.
  intros lim_s lim_t src tgt H en_s en_t inp Hvs Hvt Hvi Hb.
  destruct (H en_s en_t inp Hvs Hvt Hvi Hb) as (Ts & Tt & Hs & Ht & Heq).
  exact (shape_cfg_strong_equiv_ef_img_eq lim_s lim_t src tgt en_s en_t Ts Tt inp Hs Ht Heq).
Qed.

(* [comment removed for export] *)
Theorem shape_cfg_strong_equiv_ef_pinned :
  forall (src tgt : Image) (en_s en_t : ExecEntry) (T : TSet) (inp : ProcInput),
  realizes_cfg cfg (img_segments src) (init_cfg src source_alloc_limit en_s inp) T ->
  realizes_cfg cfg (img_segments tgt) (init_cfg tgt target_alloc_limit en_t inp) T ->
  strong_equiv_error_free_scfg cfg src tgt en_s en_t inp.
Proof.
  intros src tgt en_s en_t T inp Hs Ht.
  exact (shape_cfg_strong_equiv_ef_img source_alloc_limit target_alloc_limit
           src tgt en_s en_t T inp Hs Ht).
Qed.

Theorem shape_cfg_universal_pinned :
  forall (src tgt : Image),
  (forall en_s en_t inp,
     valid_entry src en_s inp ->
     valid_entry tgt en_t inp ->
     valid_input inp ->
     exists T : TSet,
       realizes_cfg cfg (img_segments src) (init_cfg src source_alloc_limit en_s inp) T
       /\ realizes_cfg cfg (img_segments tgt) (init_cfg tgt target_alloc_limit en_t inp) T) ->
  strong_universal_error_free_T_scfg cfg src tgt.
Proof.
  intros src tgt H en_s en_t inp Hvs Hvt Hvi.
  destruct (H en_s en_t inp Hvs Hvt Hvi) as (T & Hs & Ht).
  exact (shape_cfg_strong_equiv_ef_pinned src tgt en_s en_t T inp Hs Ht).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem shape_cfg_good_input_s :
  forall (O1 O2 : Image) (inp : ProcInput),
  (forall en1 en2,
     valid_entry O1 en1 inp -> valid_entry O2 en2 inp ->
     exists T : TSet,
       realizes_cfg cfg (img_segments O1) (init_cfg O1 source_alloc_limit en1 inp) T
       /\ realizes_cfg cfg (img_segments O2) (init_cfg O2 target_alloc_limit en2 inp) T) ->
  good_input_s cfg O1 O2 inp.
Proof.
  intros O1 O2 inp H en1 en2 H1 H2.
  destruct (H en1 en2 H1 H2) as (T & Hs & Ht).
  exact (shape_cfg_strong_equiv_ef_pinned O1 O2 en1 en2 T inp Hs Ht).
Qed.

(* [comment removed for export] *)
Lemma good_input_s_source_error_free : forall O1 O2 inp en1 en2,
  good_input_s cfg O1 O2 inp ->
  valid_entry O1 en1 inp -> valid_entry O2 en2 inp ->
  error_free (run_scfg cfg O1 source_alloc_limit en1 inp).
Proof. intros O1 O2 inp en1 en2 Hg H1 H2. exact (proj1 (Hg en1 en2 H1 H2)). Qed.

(* [comment removed for export] *)
Theorem shape_cfg_agree_s :
  forall (X Y : Image) (lim : Z) (inp : ProcInput) (T : TSet),
  (forall en, valid_entry X en inp ->
     realizes_cfg cfg (img_segments X) (init_cfg X lim en inp) T) ->
  (forall en, valid_entry Y en inp ->
     realizes_cfg cfg (img_segments Y) (init_cfg Y lim en inp) T) ->
  agree_s cfg X Y lim inp.
Proof.
  intros X Y lim inp T HX HY.
  split; [| split; [| split]].
  - intros enX enY HvX HvY tr.
    rewrite (realizes_cfg_run_traces_iff X lim enX inp T (HX enX HvX) tr).
    rewrite (realizes_cfg_run_traces_iff Y lim enY inp T (HY enY HvY) tr).
    reflexivity.
  - split; intros (en & Hv & Herr); exfalso.
    + exact (realizes_cfg_run_error_free X lim en inp T (HX en Hv) Herr).
    + exact (realizes_cfg_run_error_free Y lim en inp T (HY en Hv) Herr).
  - split; intros (en & Hv & Hall); exfalso.
    + exact (realizes_cfg_run_not_all_errors X lim en inp T (HX en Hv) Hall).
    + exact (realizes_cfg_run_not_all_errors Y lim en inp T (HY en Hv) Hall).
  - split; intros (en & Hv & Hun); exfalso.
    + exact (realizes_cfg_run_modeled X lim en inp T (HX en Hv) Hun).
    + exact (realizes_cfg_run_modeled Y lim en inp T (HY en Hv) Hun).
Qed.

(* [comment removed for export] *)
Corollary shape_cfg_agree_s_self :
  forall (X : Image) (lim : Z) (inp : ProcInput) (T : TSet),
  (forall en, valid_entry X en inp ->
     realizes_cfg cfg (img_segments X) (init_cfg X lim en inp) T) ->
  agree_s cfg X X lim inp.
Proof. intros X lim inp T HX. exact (shape_cfg_agree_s X X lim inp T HX HX). Qed.

(* [comment removed for export] *)
Lemma agree_s_self_of_traces :
  forall (X : Image) (lim : Z) (inp : ProcInput) (T : TSet),
  (forall en, valid_entry X en inp ->
     forall tr, bh_traces (run_scfg cfg X lim en inp) tr <-> T tr) ->
  agree_s cfg X X lim inp.
Proof.
  intros X lim inp T H.
  split; [| split; [| split]]; try reflexivity.
  intros en1 en2 H1 H2 tr. rewrite (H en1 H1 tr), (H en2 H2 tr). reflexivity.
Qed.

Theorem shape_cfg_error_free_input_s :
  forall (O : Image) (inp : ProcInput),
  (forall en, valid_entry O en inp ->
     exists T : TSet,
       realizes_cfg cfg (img_segments O) (init_cfg O source_alloc_limit en inp) T) ->
  error_free_input_s cfg O inp.
Proof.
  intros O inp H en Hv. destruct (H en Hv) as (T & HT).
  exact (realizes_cfg_run_error_free O source_alloc_limit en inp T HT).
Qed.

(* [comment removed for export] *)
Theorem realizes_cfg_must_exit_with :
  forall (code : word) (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) (T : TSet),
  realizes_cfg cfg (img_segments img) (init_cfg img lim en inp) T ->
  exits_only code T ->
  must_exit_with_scfg cfg code img lim en inp.
Proof.
  intros code [segs pc ph] lim [sp brk0 mbase rnd] inp T H Hex.
  cbn [must_exit_with_scfg].
  exact (realizes_cfg_must_exit cfg segs code _ T H eq_refl Hex).
Qed.

End RunLevel.

(* [comment removed for export] *)

Lemma verdict_accept_neq_reject : verdict_accept <> verdict_reject.
Proof.
  intro H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate H.
Qed.

(* [comment removed for export] *)
Theorem classifier_total_fo_of_realizes : forall (C : Image),
  (forall f : FinProcInput, valid_fin_input f ->
   forall en, valid_entry C en (to_proc_input f) ->
     exists T : TSet,
       realizes_cfg forced_only_cfg (img_segments C)
         (init_cfg C classifier_alloc_limit en (to_proc_input f)) T
       /\ (exits_only verdict_accept T \/ exits_only verdict_reject T)) ->
  classifier_total_T_fo C.
Proof.
  intros C H f Hf en Hen.
  destruct (H f Hf en Hen) as (T & Hrz & [Hex | Hex]); [left | right];
    eapply realizes_cfg_must_exit_with; eassumption.
Qed.

(* [comment removed for export] *)
Theorem decides_fo_of_realizes : forall (C : Image) (spec : ProcInput -> Prop),
  (forall f : FinProcInput, valid_fin_input f ->
   forall en, valid_entry C en (to_proc_input f) ->
     exists T : TSet,
       realizes_cfg forced_only_cfg (img_segments C)
         (init_cfg C classifier_alloc_limit en (to_proc_input f)) T
       /\ ((exits_only verdict_accept T /\ spec (to_proc_input f))
           \/ (exits_only verdict_reject T /\ ~ spec (to_proc_input f)))) ->
  decides_fo C spec.
Proof.
  intros C spec H f Hf en Hen.
  destruct (H f Hf en Hen) as (T & Hrz & [(Hex & Hs) | (Hex & Hns)]).
  - assert (Hme : must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en
                    (to_proc_input f))
      by (eapply realizes_cfg_must_exit_with; eassumption).
    split; [split; intros _; assumption | left; exact Hme].
  - assert (Hme : must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en
                    (to_proc_input f))
      by (eapply realizes_cfg_must_exit_with; eassumption).
    split; [split | right; exact Hme].
    + intros Hacc. exfalso. apply verdict_accept_neq_reject.
      exact (must_exit_with_scfg_exclusive _ _ _ _ _ _ _ Hacc Hme).
    + intros Hs. exfalso. exact (Hns Hs).
Qed.

(* [comment removed for export] *)
Corollary decides_fo_always_accept : forall (C : Image) (spec : ProcInput -> Prop),
  (forall f : FinProcInput, valid_fin_input f ->
   forall en, valid_entry C en (to_proc_input f) ->
     exists T : TSet,
       realizes_cfg forced_only_cfg (img_segments C)
         (init_cfg C classifier_alloc_limit en (to_proc_input f)) T
       /\ exits_only verdict_accept T) ->
  (forall f : FinProcInput, valid_fin_input f -> spec (to_proc_input f)) ->
  decides_fo C spec.
Proof.
  intros C spec H Hspec. apply decides_fo_of_realizes.
  intros f Hf en Hen. destruct (H f Hf en Hen) as (T & Hrz & Hex).
  exists T. split; [exact Hrz | left; split; [exact Hex | apply Hspec; exact Hf]].
Qed.
