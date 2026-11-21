(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/bzip2/bzip2_compress_target/proofs/lib/BudgetWit/Rzb.v (the relation rzb, its soundness for the budget premise, its lift to the run's segment list) and this unit's Top/Bridge.v (impl_realizes), over this unit's nodes, Top/RomStable.v and BudgetWit/NoAlloc.v; the start-state step is this unit's. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run VdsoSegs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg PropExec MState Mem Exec ITree Nodes RegsEquiv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import MSafe.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import RomBase Realize Bridge RomStable.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.BudgetWit Require Import NoAlloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

(** * [rzb]: [Top.Realize.realizes] with a no-allocation-call check at each node

    LPS 727298f3: [Run.run_budget_refused] reads the run against [run_segments segs inp sp mb]
    (the binary's segments with the run's vDSO pair appended), from [init_config] over that list.
    [NoAlloc.utree_never_refused] reads a walk over the binary's own segments, so it has to be
    lifted, as [Top.RomStable.run_init] lifts a [realizes] walk.  [realizes] records nothing
    about the calls a run makes, so the lift goes through [rzb]: the same three constructors,
    whose node constructor also asks [NoAlloc.no_alloc_pending].  That fact gives both halves of
    the budget premise: off the four allocation numbers the grant clause of
    [Run.budget_refused_at] is false ([Run.alloc_budget_refused_b_outside]), and every unfiltered
    step is an [ACFG] step ([NoAlloc.sstep_acfg_na]), so [node_ok]'s completeness half excludes
    the error steps the other clauses are premises of ([Run.budget_fault_instr_sstep_error],
    [Run.budget_fault_vdso_sstep_error], [Run.budget_fault_syscall_sstep_error]).

    - [rzb_eqv_never_refused]: no configuration the unfiltered run reaches from a state
      [RegsEquiv.cfg_eqv] to an [rzb] configuration is budget-refused (the launch's start state
      is [RegsEquiv.init_ms] up to [ms_eqv]).
    - [rzb_run_rom]: the lift to the run's segment list, from [Top.RomStable]'s node lemmas.
    - [utree_rzb]: a [NoAlloc.utree_ok] walk is an [rzb] derivation (Bridge's [impl_realizes]
      with the check), since no leaf of it is reached. *)

Section WithSegs.
Variable segs : list Segment.

Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    sys_rob segs c ->
    no_alloc_pending c ->
    (forall i, rzb (nx i) (T i)) ->
    rzb c (t_alt (fun i => t_emit (evs i) (T i)))
| rzb_halt : forall c,
    m_halted (cfg_model c) <> None ->
    rzb c t_nil
| rzb_conseq : forall c T T',
    rzb c T -> t_eq T T' -> rzb c T'.

Lemma star_cases : forall c tr c', star segs c tr c' ->
  c' = c \/ exists e c2 tr2, sstep segs c e (SNext c2) /\ star segs c2 tr2 c'.
Proof.
  intros c tr c' H. destruct H as [c0 | c1 e c2 tr2 c3 Hss Hstar].
  - left. reflexivity.
  - right. exists e, c2, tr2. split; [exact Hss | exact Hstar].
Qed.

(** Every configuration the unfiltered run reaches from an [rzb] configuration is one. *)
Lemma rzb_star : forall c T, rzb c T ->
  forall tr c', star segs c tr c' -> exists T', rzb c' T'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exists (t_alt (fun i => t_emit (evs i) (T i))). exact (rzb_node c I evs nx T i0 Hnode Hrob Hb Hcont).
    + destruct (proj2 Hnode e (SNext c2) (sstep_acfg_na segs c e (SNext c2) Hb Hss)) as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exists t_nil. exact (rzb_halt c Hh).
    + exfalso. exact (Hh (sstep_live segs c e _ Hss)).
  - exact (IH tr c' Hstar).
Qed.

(** A configuration [cfg_eqv] to an [rzb] configuration is not budget-refused. *)
Lemma rzb_not_refused_eqv : forall c0 T, rzb c0 T ->
  forall c, cfg_eqv c c0 -> ~ budget_refused_at segs c.
Proof.
  intros c0 T H;
  induction H as [c0 I evs nx T i0 Hnode Hrob Hb Hcont IH | c0 Hh | c0 T T' H IH Heq];
  intros [ms mo] [Heqv Hmo] Hr; cbn [cfg_ms cfg_model] in Heqv, Hmo.
  - destruct c0 as [ms0 mo0]. cbn [cfg_ms cfg_model] in *. subst mo0.
    (* the error clauses: an [SError] step from [c] is one from [c0], which the node excludes *)
    assert (Herr : ~ sstep segs (mkCfg ms mo) [] SError).
    { intros Hs. destruct (sstep_eqv segs ms ms0 mo [] SError Heqv Hs) as (X' & Hs0 & HX).
      destruct X'; cbn [to_eqv] in HX; try contradiction.
      destruct (proj2 Hnode [] SError (sstep_acfg_na segs _ [] SError Hb Hs0)) as (i & _ & Hbad).
      discriminate Hbad. }
    pose proof Heqv as (_ & _ & _ & Hsvc & _).
    cbn [cfg_ms cfg_model] in Hr.
    destruct Hr as (Hh & [(Hs & [ (report & Hstep & Hmat)
                               | (Hacct & fn & n & eff0 & model0 & evs0 & Hfn & Hsys & Hspec0 & Hret0 & Hh0 & Hmat0) ])
                        | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])]);
      cbn [cfg_ms cfg_model] in *.
    + exact (Herr (budget_fault_instr_sstep_error segs ms mo report Hh Hs Hstep Hmat)).
    + exact (Herr (budget_fault_vdso_sstep_error segs ms mo fn n eff0 model0 evs0
                     Hh Hs Hacct Hfn Hsys Hspec0 Hret0 Hh0 Hmat0)).
    + (* the grant clause: the call pending at [c] is [c0]'s, not an allocation call *)
      assert (Hx0 : ms_svc_pending ms0 = Some x8) by (rewrite <- Hsvc; exact Hx8).
      rewrite (sys_input_eqv segs ms ms0 x8 Heqv) in Hgr.
      pose proof (alloc_budget_refused_b_outside (sys_input segs ms0 x8) mo (Hb x8 Hx0)) as Hf.
      change (alloc_budget_refused_b (sys_input segs ms0 x8) mo = true) in Hgr. congruence.
    + exact (Herr (budget_fault_syscall_sstep_error segs ms mo x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
  - destruct Hr as [Hn _]. cbn [cfg_model] in Hn. apply Hh. rewrite <- Hmo. exact Hn.
  - exact (IH (mkCfg ms mo) (conj Heqv Hmo) Hr).
Qed.

(** No configuration the unfiltered run reaches from a state [cfg_eqv] to an [rzb]
    configuration is budget-refused. *)
Theorem rzb_eqv_never_refused : forall c0 T c, rzb c0 T -> cfg_eqv c c0 ->
  ~ reaches_budget_refused segs c.
Proof.
  intros c0 T c H Heqv (tr & c' & Hstar & Hr).
  destruct (star_eqv segs c tr c' Hstar c0 Heqv) as (c0' & Hstar0 & Heqv').
  destruct (rzb_star c0 T H tr c0' Hstar0) as (T' & H').
  exact (rzb_not_refused_eqv c0' T' H' c' Heqv' Hr).
Qed.

(** ** Building [rzb]: instruction steps and a [NoAlloc.utree_ok] walk *)

Lemma no_alloc_pending_instr : forall ms mo, ms_svc_pending ms = None -> no_alloc_pending (mkCfg ms mo).
Proof. intros ms mo H x8 Hx. cbn [cfg_ms] in Hx. congruence. Qed.

Lemma rzb_nonempty : forall c T, rzb c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma rzb_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  rzb (mkCfg ms' model) T ->
  rzb (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  apply (rzb_conseq (mkCfg ms model) (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzb_node (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model) (fun _ => T) tt).
    + exact (node_instr segs ms model ms' Hh Hlazy Hsvc Hstep).
    + apply sys_rob_instr. exact Hsvc.
    + exact (no_alloc_pending_instr ms model Hsvc).
    + intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply rzb_nonempty; exact Hc ].
Qed.

Lemma rzb_msteps : forall ms ms' mo T,
  m_halted mo = None -> m_vm_lazy mo = [] ->
  msteps segs ms ms' -> rzb (mkCfg ms' mo) T -> rzb (mkCfg ms mo) T.
Proof.
  intros ms ms' mo T Hh Hlz Hs. induction Hs; intros HR; [exact HR|].
  destruct H as [Hsvc Hst]. eapply rzb_step; eauto.
Qed.

(** A walk over a tree with no allocation node, safe at the model, whose leaves are never
    reached ([QP]), is an [rzb] derivation: [Top.Bridge.impl_realizes] with the check, which
    [NoAlloc.at_node_na] gives at each node. *)
Theorem utree_rzb {R} : forall (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop),
  (forall r ms mo, Q r ms -> P r mo -> False) ->
  forall (t : itree node R) ms mo, utree_ok segs Q P t ms mo ->
  rzb (mkCfg ms mo) (tshape node nstep nexit t mo (fun _ _ => t_nil)).
Proof.
  intros Q P QP t. induction t as [r | n k IH]; intros ms mo (Himpl & Hwf & Hh & Hm & Hna);
    cbn in Himpl, Hwf; cbn [tshape].
  - destruct Himpl as (ms' & _ & HQ). exfalso. exact (QP r ms' mo HQ Hwf).
  - destruct Himpl as (ms1 & Hs & Hat & Hk). destruct Hwf as [Hsafe Hwk]. destruct Hna as [Hnn Hnak].
    pose proof (nodes_sound segs) as NS.
    eapply rzb_msteps; [exact Hh| exact (minv_nolazy mo Hm)| exact Hs|].
    set (nx := fun i : nindex node nstep nexit n mo =>
                 match i with
                 | inl (exist _ p _) => mkCfg (nret ms1 (fst (fst p))) (snd (fst p))
                 | inr (exist _ p _) => mkCfg ms1 (snd p)
                 end).
    set (TT := fun i : nindex node nstep nexit n mo =>
                 match i with
                 | inl (exist _ p _) => tshape node nstep nexit (k (fst (fst p))) (snd (fst p)) (fun _ _ => t_nil)
                 | inr _ => t_nil
                 end).
    assert (Hnode : node_ok segs (mkCfg ms1 mo) (nindex node nstep nexit n mo) (ni_evs node nstep nexit n mo) nx).
    { split.
      * intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hex]]; cbn.
        -- destruct (ns_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hm Hsafe Hst) as (_ & _ & Hss). exact Hss.
        -- destruct (ns_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hm Hsafe Hex) as [_ Hss]. exact Hss.
      * intros e st Hss.
        destruct (ns_complete _ _ _ _ _ _ _ _ NS n ms1 mo e st Hat Hh Hm Hsafe Hss)
          as [(rsp & mo' & -> & Hst) | (code & mo' & -> & Hex & ->)].
        -- exists (inl (exist _ (rsp, mo', e) Hst)). cbn. auto.
        -- exists (inr (exist _ (code, mo') Hex)). cbn. auto. }
    assert (Hrob : sys_rob segs (mkCfg ms1 mo)) by exact (ns_rob _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hm Hsafe).
    assert (Hb : no_alloc_pending (mkCfg ms1 mo)) by (intros x8 Hx; exact (at_node_na segs n ms1 x8 Hat Hnn Hx)).
    assert (Hcont : forall i, rzb (nx i) (TT i)).
    { intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hex]]; cbn.
      * destruct (ns_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hm Hsafe Hst) as (Hh' & Hm' & _).
        apply IH. exact (conj (Hk rsp) (conj (Hwk rsp mo' evs Hst) (conj Hh' (conj Hm' (Hnak rsp))))).
      * destruct (ns_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hm Hsafe Hex) as [Hh' _].
        apply rzb_halt. cbn. rewrite Hh'. discriminate. }
    change (rzb (mkCfg ms1 mo) (t_alt (fun i : nindex node nstep nexit n mo => t_emit (ni_evs node nstep nexit n mo i) (TT i)))).
    destruct (ns_progress _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hm Hsafe) as [(rsp0 & mo0 & evs0 & Hst0) | (code & mo' & Hex)].
    + exact (rzb_node _ (nindex node nstep nexit n mo) (ni_evs node nstep nexit n mo) nx TT (inl (exist _ (rsp0, mo0, evs0) Hst0)) Hnode Hrob Hb Hcont).
    + exact (rzb_node _ (nindex node nstep nexit n mo) (ni_evs node nstep nexit n mo) nx TT (inr (exist _ (code, mo') Hex)) Hnode Hrob Hb Hcont).
Qed.

End WithSegs.

(** ** The walk over the binary's own segments, lifted to the run

    As [Top.RomStable.realizes_wrom], [realizes_app_tail] and [realizes_run_rom] for [realizes]:
    every node-level step is RomStable's own, and [no_alloc_pending] reads [ms_svc_pending]
    alone, which a change of the read-only backing leaves alone. *)

Lemma no_alloc_pending_cwrom : forall c r, no_alloc_pending c -> no_alloc_pending (cwrom c r).
Proof. intros [ms model] r H. exact H. Qed.

Section RzbWrom.
  Variable segs : list Segment.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_wrom : forall c T, rzb segs c T ->
    forall r, rom_ext (ms_rom (cfg_ms c)) r -> rzb segs (cwrom c r) T.
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq];
    intros r Hr.
    - apply (rzb_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
      + eapply node_wrom; eassumption.
      + eapply sys_rob_wrom; eassumption.
      + apply no_alloc_pending_cwrom; exact Hb.
      + intros i. apply IH.
        match goal with |- rom_ext ?x _ => replace x with (ms_rom (cfg_ms c)) end;
          [exact Hr|].
        symmetry. eapply node_rom; eassumption.
    - apply rzb_halt. exact Hh.
    - eapply rzb_conseq; [apply IH; exact Hr | exact Heq].
  Qed.
End RzbWrom.

Section RzbAppTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_app_tail : forall c T, rzb segs c T -> rzb (segs ++ tail) c T.
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq].
    - apply (rzb_node (segs ++ tail) c I evs nx T i0).
      + eapply node_ok_app_tail; eassumption.
      + eapply sys_rob_app_tail; eassumption.
      + exact Hb.
      + exact IH.
    - apply rzb_halt. exact Hh.
    - eapply rzb_conseq; [exact IH | exact Heq].
  Qed.
End RzbAppTail.

Theorem rzb_run_segments : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  rzb segs c T -> rzb (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply (rzb_app_tail segs _
           (fun s Hs => vdso_segments_nx _ _ _ s Hs)
           (fun s Hs => vdso_segments_nw _ _ _ s Hs) Hvi).
  exact H.
Qed.

(** From any start whose backing is the binary's own ([RegsEquiv.init_ms] is one): with the
    run's backing it is an [rzb] start of the run ([Top.RomStable.realizes_run_rom]'s form). *)
Theorem rzb_run_rom : forall segs inp (sp mb : word) ms mo T,
  vdso_image segs = None ->
  ms_rom ms = seg_rom1 segs ->
  rzb segs (mkCfg ms mo) T ->
  rzb (run_segments segs inp sp mb) (mkCfg (wrom ms (seg_rom1 (run_segments segs inp sp mb))) mo) T.
Proof.
  intros segs inp sp mb ms mo T Hvi Hrom H.
  change (mkCfg (wrom ms (seg_rom1 (run_segments segs inp sp mb))) mo)
    with (cwrom (mkCfg ms mo) (seg_rom1 (run_segments segs inp sp mb))).
  apply rzb_run_segments; [exact Hvi|].
  apply (rzb_wrom segs Hvi); [exact H|].
  cbn [cfg_ms]. rewrite Hrom. apply rom_ext_run_segments.
Qed.
