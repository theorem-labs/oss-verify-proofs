(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import CatSim ShapeAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

Section Facts.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs cfg c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs cfg c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh H. inversion H as [c0 | c1 e c2 tr2 c3 Hs Hst]; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hs.
Qed.

Lemma star_cfg_one : forall c e c',
  sstep_cfg segs cfg c e (SNext c') -> star_cfg segs cfg c e c'.
Proof.
  intros c e c' H. rewrite <- (app_nil_r e).
  eapply star_cfg_step; [exact H | apply star_cfg_refl].
Qed.

(* [comment removed for export] *)
Definition silent_inv (S : config -> Prop) : Prop :=
  forall c1 e st, S c1 -> sstep_cfg segs cfg c1 e st -> e = [] /\ exists c2, st = SNext c2 /\ S c2.

Lemma star_cfg_silent_inv : forall (S : config -> Prop), silent_inv S ->
  forall c tr c', star_cfg segs cfg c tr c' -> S c -> tr = [] /\ S c'.
Proof.
  intros S Hinv c tr c' Hstar. induction Hstar as [c | c1 e c2 tr c3 Hs Hst IH]; intros HS.
  - split; [reflexivity | exact HS].
  - destruct (Hinv c1 e (SNext c2) HS Hs) as [-> (c2' & Heq & HS2)]. inversion Heq; subst c2'.
    destruct (IH HS2) as [-> HS3]. split; [reflexivity | exact HS3].
Qed.

Lemma obs_trace_cfg_nil : forall c, obs_trace_cfg segs cfg c [].
Proof. intros c. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil]. Qed.

End Facts.

(* [comment removed for export] *)

Section WithCfg.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

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
| rzc_spin : forall c (S : config -> Prop),
    S c ->
    silent_inv segs cfg S ->
    False ->      (* [comment removed for export] *)
    realizes_cfg c t_nil
| rzc_conseq : forall c T T',
    realizes_cfg c T -> t_eq T T' -> realizes_cfg c T'.

Lemma realizes_cfg_nonempty : forall c T, realizes_cfg c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma realizes_cfg_pclosed : forall c T, realizes_cfg c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

Lemma realizes_cfg_star_only : forall c T, realizes_cfg c T ->
  forall tr c', star_cfg segs cfg c tr c' -> T tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil segs cfg c tr c' Hh Hstar) as [-> _]. reflexivity.
  - destruct (star_cfg_silent_inv segs cfg S0 Hinv c tr c' Hstar HS) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

Lemma realizes_cfg_admits : forall c T, realizes_cfg c T ->
  forall tr, T tr -> obs_trace_cfg segs cfg c tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
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
  - apply realizes_cfg_admits; exact H.
Qed.

Lemma realizes_cfg_step : forall c T e c',
  realizes_cfg c T -> sstep_cfg segs cfg c e (SNext c') -> exists T', realizes_cfg c' T'.
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - destruct (Hinv c e (SNext c') HS Hss) as [_ (c2 & Heq2 & HS2)]. inversion Heq2; subst c2.
    exfalso. assumption.
  - eapply IH; exact Hss.
Qed.

Lemma realizes_cfg_no_sserror : forall c T e,
  realizes_cfg c T -> ~ sstep_cfg segs cfg c e SError.
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - destruct (Hinv c e SError HS Hss) as [_ (c2 & Hbad & _)]. discriminate Hbad.
  - eapply IH; exact Hss.
Qed.

Lemma realizes_cfg_star : forall c T tr c',
  realizes_cfg c T -> star_cfg segs cfg c tr c' -> exists T', realizes_cfg c' T'.
Proof.
  intros c T tr c' H Hstar. revert T H.
  induction Hstar as [c | c1 e c2 tr c3 Hs Hst IH]; intros T H.
  - exists T. exact H.
  - destruct (realizes_cfg_step c1 T e c2 H Hs) as (T2 & H2). exact (IH T2 H2).
Qed.

(* [comment removed for export] *)
Theorem realizes_cfg_no_error : forall c T, realizes_cfg c T -> ~ reaches_error_cfg segs cfg c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  destruct (realizes_cfg_star c T tr c' H Hstar) as (T' & H').
  exact (realizes_cfg_no_sserror c' T' evs H' Herr).
Qed.

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
Lemma rzc_silent_all : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok_cfg c I (fun _ => []) nx ->
  (forall i, realizes_cfg (nx i) T) ->
  realizes_cfg c T.
Proof.
  intros c I nx T i0 Hnode Hc.
  assert (HT0 : T []) by (eapply realizes_cfg_nonempty; apply (Hc i0)).
  apply (rzc_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (rzc_node c I (fun _ => []) nx (fun _ => T) i0 Hnode). exact Hc.
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intro Htr. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.

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
Lemma rzc_silent_mix : forall c (I : Type) (nx : I -> config) (good : I -> bool) (T : TSet) (i0 : I),
  node_ok_cfg c I (fun _ => []) nx ->
  good i0 = true ->
  (forall i, good i = true -> realizes_cfg (nx i) T) ->
  (forall i, good i = false -> realizes_cfg (nx i) t_nil) ->
  realizes_cfg c T.
Proof.
  intros c I nx good T i0 Hnode Hg0 HG HB.
  assert (HT0 : T []) by (eapply realizes_cfg_nonempty; apply (HG i0 Hg0)).
  apply (rzc_conseq c (t_alt (fun i : I => t_emit [] (if good i then T else t_nil)))).
  - apply (rzc_node c I (fun _ => []) nx (fun i => if good i then T else t_nil) i0 Hnode).
    intro i. destruct (good i) eqn:E; [apply HG | apply HB]; exact E.
  - intro tr. split.
    + intros [i Hi]. destruct (good i).
      * exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
      * apply (t_emit_nil_eq t_nil eq_refl tr) in Hi. unfold t_nil in Hi. subst tr. exact HT0.
    + intro Htr. exists i0. rewrite Hg0. exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_reindex : forall c (I J : Type) (f : J -> I) (evs : I -> list event) (nx : I -> config),
  (forall i, exists j, f j = i) ->
  node_ok_cfg c I evs nx ->
  node_ok_cfg c J (fun j => evs (f j)) (fun j => nx (f j)).
Proof.
  intros c I J f evs nx Hsurj [Hcomp Hsound]. split.
  - intro j. apply Hcomp.
  - intros e st Hss. destruct (Hsound e st Hss) as (i & -> & ->).
    destruct (Hsurj i) as (j & <-). exists j. split; reflexivity.
Qed.

End WithCfg.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem shape_strong_equiv_ef_cfg :
  forall (cfg : SpuriousCfg) (segs1 : list Segment) (pc1 : N) (ph1 : PhdrInfo)
         (segs2 : list Segment) (pc2 : N) (ph2 : PhdrInfo)
         (en1 en2 : ExecEntry) (inp : ProcInput) (T : TSet),
  realizes_cfg segs1 cfg
    (init_config segs1 pc1 ph1 (en_sp en1) (en_brk en1) (en_mmap_base en1) (en_draw en1)
                 source_alloc_limit inp) T ->
  realizes_cfg segs2 cfg
    (init_config segs2 pc2 ph2 (en_sp en2) (en_brk en2) (en_mmap_base en2) (en_draw en2)
                 target_alloc_limit inp) T ->
  strong_equiv_error_free_scfg cfg (mkImage segs1 pc1 ph1) (mkImage segs2 pc2 ph2) en1 en2 inp.
Proof.
  intros cfg segs1 pc1 ph1 segs2 pc2 ph2 [sp1 brk1 mb1 d1] [sp2 brk2 mb2 d2] inp T H1 H2.
  cbn [en_sp en_brk en_mmap_base en_draw] in H1, H2.
  unfold strong_equiv_error_free_scfg, error_free. cbn [run_scfg bh_errors bh_traces].
  split; [exact (realizes_cfg_no_error _ _ _ _ H1) |].
  split; [exact (realizes_cfg_no_error _ _ _ _ H2) |].
  intro tr. rewrite (realizes_cfg_obs_iff _ _ _ _ H1 tr), (realizes_cfg_obs_iff _ _ _ _ H2 tr).
  reflexivity.
Qed.

(* [comment removed for export] *)

Section Transparent.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
Definition cfg_transparent (c : config) : Prop :=
  forall e st, sstep segs c e st -> sstep_cfg segs cfg c e st.

Lemma transparent_instr : forall ms model,
  ms_svc_pending ms = None -> cfg_transparent (mkCfg ms model).
Proof.
  intros ms model Hsvc e st H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H1; discriminate H1 end).
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
Qed.

Lemma transparent_family_on : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  injected_family_off cfg (sys_input segs ms x8) = false ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hoff e st H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
    match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H1; injection H1; intro; subst y end.
  - eapply sstep_cfg_syscall; try eassumption. apply spurious_refusal_family_on. exact Hoff.
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    apply spurious_refusal_family_on. exact Hoff.
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

(* [comment removed for export] *)
Lemma transparent_uninjected : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  injected_arm (bv_unsigned x8) = None ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hno.
  apply (transparent_family_on ms model x8 Hsvc).
  unfold injected_family_off. cbn [sys_input in_sysno]. rewrite Hno. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma injected_family_off_nonalloc : forall (i : SyscallInput),
  sc_fs cfg = true -> sc_fd cfg = true -> sc_net cfg = true ->
  sc_cred cfg = true -> sc_intr cfg = true ->
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  injected_family_off cfg i = false.
Proof.
  intros i Hfs Hfd Hnet Hcred Hintr Hnin. unfold injected_family_off.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [a |] eqn:E; [| reflexivity].
  destruct (ia_family a) eqn:Ef; cbn [family_may_fail];
    first [ rewrite Hfs | rewrite Hfd | rewrite Hnet | rewrite Hcred | rewrite Hintr | idtac ];
    try reflexivity.
  exfalso. apply Hnin. exact (alloc_family_dispatched _ a E Ef).
Qed.

Lemma transparent_nonalloc : forall ms model x8,
  sc_fs cfg = true -> sc_fd cfg = true -> sc_net cfg = true ->
  sc_cred cfg = true -> sc_intr cfg = true ->
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 H1 H2 H3 H4 H5 Hsvc Hnin.
  apply (transparent_family_on ms model x8 Hsvc).
  apply injected_family_off_nonalloc; assumption.
Qed.

Lemma node_ok_cfg_of_transparent : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
  node_ok segs c I evs nx ->
  cfg_transparent c ->
  node_ok_cfg segs cfg c I evs nx.
Proof.
  intros c I evs nx [Hcomp Hsound] Ht. split.
  - intro i. apply Ht. apply Hcomp.
  - intros e st Hss. apply Hsound. eapply sstep_cfg_sub; exact Hss.
Qed.

(* [comment removed for export] *)
Lemma node_instr_cfg : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep.
  apply node_ok_cfg_of_transparent; [apply node_instr; assumption | apply transparent_instr; exact Hsvc].
Qed.

Lemma rzc_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes_cfg segs cfg (mkCfg ms' model) T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rzc_silent1; [apply node_instr_cfg; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rzc_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  realizes_cfg segs cfg (mkCfg ms' model) T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rzc_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                   | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rzc_node_transparent : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                                    (T : I -> TSet) (i0 : I),
  node_ok segs c I evs nx ->
  cfg_transparent c ->
  (forall i, realizes_cfg segs cfg (nx i) (T i)) ->
  realizes_cfg segs cfg c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 Hn Ht Hc.
  apply (rzc_node segs cfg c I evs nx T i0); [apply node_ok_cfg_of_transparent; assumption | exact Hc].
Qed.

End Transparent.

(* [comment removed for export] *)

Section Filter.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
Definition ret_of (c : config) : word := ms_gpr (cfg_ms c) 0.

Lemma ret_of_apply_effect : forall ms eff model,
  ret_of (mkCfg (advance_past_svc (apply_effect ms eff)) model) = eff_ret eff.
Proof.
  intros ms eff model. unfold ret_of, ms_gpr. cbn [cfg_ms advance_past_svc apply_effect ms_regs].
  unfold set_reg.
  destruct (bv_eqb _ _) eqn:E; [vm_compute in E; discriminate E |].
  cbn [ms_regs]. unfold Sem.reg_get.
  replace (Z_to_bv 5 (10 + Z.of_nat 0)) with (10 : reg) by (apply bv_eq; reflexivity).
  rewrite bvmap_get_set_same. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_svc_inv : forall ms model x8 e c',
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs cfg (mkCfg ms model) e (SNext c') ->
  (exists eff model' model'',
     syscall_spec (sys_input segs ms x8) model (Ok eff model' e)
     /\ ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff
     /\ m_halted model' = None
     /\ c' = mkCfg (advance_past_svc (apply_effect ms eff)) model'')
  \/ (exists model', m_halted model' <> None /\ c' = mkCfg ms model').
Proof.
  intros ms model x8 e c' Hsvc H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
    match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H1; injection H1; intro; subst y end.
  - left. do 3 eexists. split; [eassumption |]. split; [eassumption |]. split; [eassumption | reflexivity].
  - right. eexists. split; [| reflexivity]. match goal with H1 : m_halted ?m = Some _ |- _ => rewrite H1; discriminate end.
  - right. eexists. split; [| reflexivity].
    match goal with H1 : m_killed ?m = Some _ |- _ =>
      intro Hn; rewrite (m_killed_of_m_halted_none _ Hn) in H1; discriminate H1 end.
Qed.

Lemma sstep_svc_inv' : forall ms model x8 e c',
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e (SNext c') ->
  (exists eff model' model'',
     syscall_spec (sys_input segs ms x8) model (Ok eff model' e)
     /\ m_halted model' = None
     /\ c' = mkCfg (advance_past_svc (apply_effect ms eff)) model'')
  \/ (exists model', m_halted model' <> None /\ c' = mkCfg ms model').
Proof.
  intros ms model x8 e c' Hsvc H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
    match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H1; injection H1; intro; subst y end.
  - left. do 3 eexists. split; [eassumption |]. split; [eassumption | reflexivity].
  - right. eexists. split; [| reflexivity]. match goal with H1 : m_halted ?m = Some _ |- _ => rewrite H1; discriminate end.
  - right. eexists. split; [| reflexivity].
    match goal with H1 : m_killed ?m = Some _ |- _ =>
      intro Hn; rewrite (m_killed_of_m_halted_none _ Hn) in H1; discriminate H1 end.
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_filter : forall ms model x8 (G R : Type)
    (evs : G + R -> list event) (nx : G + R -> config) (g0 : G),
  ms_svc_pending ms = Some x8 ->
  node_ok segs (mkCfg ms model) (G + R) evs nx ->
  injected_family_off cfg (sys_input segs ms x8) = true ->
  (forall k, m_halted (cfg_model (nx k)) = None) ->
  (forall g, refusal_b (sys_input segs ms x8) model (ret_of (nx (inl g))) = false) ->
  (forall r, refusal_b (sys_input segs ms x8) model (ret_of (nx (inr r))) = true) ->
  node_ok_cfg segs cfg (mkCfg ms model) G (fun g => evs (inl g)) (fun g => nx (inl g)).
Proof.
  intros ms model x8 G R evs nx g0 Hsvc [Hcomp Hsound] Hoff Hnh Hg Hr.
  (* [comment removed for export] *)
  assert (Hex : exists eff' m' evs',
             syscall_spec (sys_input segs ms x8) model (Ok eff' m' evs')
             /\ refusal_b (sys_input segs ms x8) model (eff_ret eff') = false).
  { destruct (sstep_svc_inv' ms model x8 _ _ Hsvc (Hcomp (inl g0)))
      as [(eff & m' & m'' & Hs & _ & Heq) | (m' & Hh & Heq)].
    - exists eff, m', (evs (inl g0)). split; [exact Hs |].
      rewrite <- (ret_of_apply_effect ms eff m''), <- Heq. apply Hg.
    - exfalso. apply Hh. pose proof (Hnh (inl g0)) as H0. rewrite Heq in H0. exact H0. }
  split.
  - intro g. specialize (Hcomp (inl g)).
    inversion Hcomp; subst;
      try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
      match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
        rewrite Hsvc in H1; injection H1; intro; subst y end.
    + eapply sstep_cfg_syscall; try eassumption.
      apply spurious_refusal_not_refusal.
      match goal with H1 : mkCfg (advance_past_svc (apply_effect ms ?eff)) ?m = nx (inl g) |- _ =>
        pose proof (Hg g) as Hgg; rewrite <- H1, ret_of_apply_effect in Hgg; exact Hgg end.
    + exfalso. match goal with H1 : mkCfg ms ?m = nx (inl g), H2 : m_halted ?m = Some _ |- _ =>
        pose proof (Hnh (inl g)) as H0; rewrite <- H1 in H0; cbn in H0; rewrite H2 in H0; discriminate H0 end.
    + exfalso. match goal with H1 : mkCfg ms ?m = nx (inl g), H2 : m_killed ?m = Some _ |- _ =>
        pose proof (Hnh (inl g)) as H0; rewrite <- H1 in H0; cbn in H0;
        rewrite (m_killed_of_m_halted_none _ H0) in H2; discriminate H2 end.
  - intros e st Hss.
    destruct (Hsound e st (sstep_cfg_sub segs cfg _ _ _ Hss)) as ([g | r] & -> & ->).
    + exists g. split; reflexivity.
    + exfalso.
      destruct (sstep_cfg_svc_inv ms model x8 _ _ Hsvc Hss)
        as [(eff & m' & m'' & Hs & Hns & _ & Heq) | (m' & Hh & Heq)].
      * apply Hns. split; [exact Hoff |]. split; [| exact Hex].
        rewrite <- (ret_of_apply_effect ms eff m''), <- Heq. apply Hr.
      * apply Hh. pose proof (Hnh (inr r)) as H0. rewrite Heq in H0. exact H0.
Qed.

(* [comment removed for export] *)
Lemma node_sys_cfg : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) (EV i))) ->
  (forall i, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model (E i)) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> m_halted m' = None) ->
  (forall i, m_vm_lazy (M i) = []) ->
  node_ok_cfg segs cfg (mkCfg ms model) I EV
          (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)).
Proof.
  intros ms model x8 I E M EV Hh Hsvc Hcomp Hns Hsound Hnu Hnh Hnl. split.
  - intro i. apply (sstep_cfg_syscall segs cfg ms model x8 (E i) (M i) (M i) (EV i));
      [exact Hh | exact Hsvc | apply Hcomp | apply Hns | apply (Hnh _ _ _ (Hcomp i))
       | apply materialize_model_accesses_no_lazy; apply Hnl].
  - intros e st Hss. inversion Hss; subst;
      try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
      match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
        rewrite Hsvc in H1; injection H1; intro; subst y end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?e1), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
          destruct (Hsound _ _ _ Hs Hn) as (i & -> & -> & ->);
          rewrite (materialize_model_accesses_no_lazy _ _ (Hnl i)) in Hm;
          injection Hm; intro; subst m2; exists i; split; reflexivity
      end.
    + exfalso. match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?e1), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = None |- _ =>
          destruct (Hsound _ _ _ Hs Hn) as (i & -> & -> & ->);
          rewrite (materialize_model_accesses_no_lazy _ _ (Hnl i)) in Hm; discriminate Hm
      end.
    + exfalso. match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?e1), Hc : m_halted ?m1 = Some _ |- _ =>
          rewrite (Hnh _ _ _ Hs) in Hc; discriminate Hc
      end.
    + exfalso. match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?e1), Hk : m_killed ?m1 = Some _ |- _ =>
          rewrite (m_killed_of_m_halted_none _ (Hnh _ _ _ Hs)) in Hk; discriminate Hk
      end.
    + exfalso. apply Hnu. assumption.
Qed.

End Filter.
