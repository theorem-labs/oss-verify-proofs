(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Common/RealizesCfg.v and Common/SysNodesCfg.v: the relation realizes_cfg with a no-allocation check at each node (rzb), its soundness for the budget premise, and the node lemmas the start-up and usage path need, restated over rzb. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's segment list run_segments; RomBase.sys_rob at the system-call nodes; the vDSO clause of budget_refused_at). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RomBase RomStable.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** * [rzb]: [RealizesCfg.realizes_cfg] with a no-allocation check at each node

    [realizes_cfg segs cfg c T] ties a trace set to the one-step families of
    the configurations the run FILTERED by [cfg] reaches.  It has no cut, but a
    derivation records nothing about the configurations it passes, so no
    [realizes_cfg] proof says that a run is never refused by the budget.

    [rzb segs cfg] has the same three constructors; its node constructor asks,
    besides [node_ok_cfg segs cfg], for [nonalloc segs c]: if a system call is
    pending at [c], its number is not one of [Run.alloc_mark_sysnos] (brk 214,
    mremap 216, mmap 222, mprotect 226).  That one fact does two jobs.

    - It is the grant check: [Run.alloc_budget_refused_b] answers [false]
      outside those four numbers ([Run.alloc_budget_refused_b_outside]).
    - It closes the gap a filtered index leaves.  The released derivations are
      at [DriverCfg.DCFG], which is [alloc_only_cfg false]: a filter, whose run
      reaches FEWER configurations than the unfiltered run.  The budget premise
      is shown false through the unfiltered run, so a filtered [node_ok_cfg]
      says nothing about an unfiltered step the filter drops.  For a
      configuration whose filter turns off only the four allocation numbers
      ([RealizesCfg.alloc_only_false_off_no]), [nonalloc] gives
      [RealizesCfg.svc_unfiltered], and [RealizesCfg.sstep_cfg_of_sstep] makes
      every unfiltered step from the node a filtered step, which node
      completeness covers.

    [rzb_star_safe] therefore follows the UNFILTERED run, [rzb_never_refused]
    is [~ Run.reaches_budget_refused], and [rzb_never_refused_cfg] gives every
    spurious-failure configuration through [Run.reaches_budget_refused_cfg_sub].
    The two first-touch clauses of [Run.budget_refused_at] are premises of an
    unfiltered [SError] step ([Run.budget_fault_instr_sstep_error],
    [Run.budget_fault_syscall_sstep_error]), which node completeness excludes. *)

Section g.
Variable segs : list Segment.

(** If a system call is pending at [c], it is not an allocation call. *)
Definition nonalloc (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    ~ In (bv_unsigned (in_sysno (sys_input segs (cfg_ms c) x8))) alloc_mark_sysnos.

Lemma nonalloc_instr : forall ms model,
  ms_svc_pending ms = None -> nonalloc (mkCfg ms model).
Proof. intros ms model Hsvc x8 Hx. cbn [cfg_ms] in Hx. rewrite Hsvc in Hx. discriminate Hx. Qed.

Lemma nonalloc_sys : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned (in_sysno (sys_input segs ms x8))) alloc_mark_sysnos ->
  nonalloc (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hn y Hy. cbn [cfg_ms] in Hy |- *.
  rewrite Hsvc in Hy. injection Hy as <-. exact Hn.
Qed.

(** The grant check. *)
Lemma grant_of_nonalloc : forall ms model x8,
  nonalloc (mkCfg ms model) -> ms_svc_pending ms = Some x8 ->
  alloc_budget_refused_b (sys_input segs ms x8) model = false.
Proof. intros ms model x8 Hn Hx. apply alloc_budget_refused_b_outside. exact (Hn x8 Hx). Qed.
End g.

(** A system call number that is not one of the four. *)
Lemma not_alloc_no : forall (i : SyscallInput) (no : Z),
  bv_unsigned (in_sysno i) = no -> existsb (Z.eqb no) alloc_mark_sysnos = false ->
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof.
  intros i no Hno Hb Hin. rewrite Hno in Hin.
  assert (Ht : existsb (Z.eqb no) alloc_mark_sysnos = true).
  { apply existsb_exists. exists no. split; [exact Hin | apply Z.eqb_refl]. }
  rewrite Ht in Hb. discriminate Hb.
Qed.

Section WithSegsCfg.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok_cfg segs cfg c I evs nx ->
    (* the node's system call reads the same over a larger read-only backing
       ([RealizesCfg.rzc_node] asks the same, in the same place), so a walk over the
       binary's own segments lifts to the run's segment list ([rzb_run_init]) *)
    RomBase.sys_rob segs c ->
    nonalloc segs c ->
    (forall i, rzb (nx i) (T i)) ->
    rzb c (t_alt (fun i => t_emit (evs i) (T i)))
| rzb_halt : forall c,
    m_halted (cfg_model c) <> None ->
    rzb c t_nil
| rzb_conseq : forall c T T',
    rzb c T -> t_eq T T' -> rzb c T'.

Lemma rzb_nonempty : forall c T, rzb c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hn Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

(** [RealizesCfg.rzc_silent1] over [rzb]. *)
Lemma rzb_silent1 : forall c c' T,
  node_ok_cfg segs cfg c unit (fun _ => []) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  nonalloc segs c ->
  rzb c' T ->
  rzb c T.
Proof.
  intros c c' T Hnode Hrob Hn Hc.
  apply (rzb_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzb_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob Hn).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply rzb_nonempty; exact Hc ].
Qed.

(** [RealizesCfg.rzc_emit1] over [rzb]. *)
Lemma rzb_emit1 : forall c c' e T,
  node_ok_cfg segs cfg c unit (fun _ => e) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  nonalloc segs c ->
  rzb c' T ->
  rzb c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hn Hc.
  apply (rzb_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rzb_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob Hn).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(** [RealizesCfg.rzc_step_acct] over [rzb]: an instruction has no pending
    system call. *)
Lemma rzb_step_acct : forall ms model ms' model' T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  rzb (mkCfg ms' model') T ->
  rzb (mkCfg ms model) T.
Proof.
  intros ms model ms' model' T Hh Hsvc Hacc Hc.
  eapply rzb_silent1;
    [ apply (node_instr_cfg segs cfg); eassumption
    | apply RomBase.sys_rob_instr; cbn [cfg_ms]; exact Hsvc
    | apply nonalloc_instr; exact Hsvc
    | exact Hc ].
Qed.

(** [RealizesCfg.rzc_step] over [rzb]. *)
Lemma rzb_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  rzb (mkCfg ms' model) T ->
  rzb (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  apply (rzb_step_acct ms model ms' model T Hh Hsvc); [| exact Hc].
  rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(** [SysNodesCfg.rzc_sys] over [rzb]: a system call node, with its number
    outside the four allocation numbers. *)
Lemma rzb_sys : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event) (T : I -> TSet) (i0 : I),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned (in_sysno (sys_input segs ms x8))) alloc_mark_sysnos ->
  (forall j, syscall_spec (sys_input segs ms x8) model (Ok (E j) (M j) (EV j))) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     exists j, eff = E j /\ m' = M j /\ evs = EV j) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff) ->
  (forall j, m_halted (M j) = None) ->
  (forall j, m_vm_lazy (M j) = []) ->
  RomBase.sys_rob segs (mkCfg ms model) ->
  (forall j, rzb (mkCfg (advance_past_svc (apply_effect ms (E j))) (M j)) (T j)) ->
  rzb (mkCfg ms model) (t_alt (fun j => t_emit (EV j) (T j))).
Proof.
  intros ms model x8 I E M EV T i0 Hh Hsvc Hna Hcomp Hsound Hnu Hns HhM HlM Hrob HK.
  apply (rzb_node (mkCfg ms model) I EV
           (fun j => mkCfg (advance_past_svc (apply_effect ms (E j))) (M j)) T i0);
    [| exact Hrob | exact (nonalloc_sys segs ms model x8 Hsvc Hna) | exact HK].
  apply (node_sys_cfg_nl segs cfg ms model x8 I E M EV Hh Hsvc Hcomp); try assumption.
  - intros j. apply Hns.
  - intros eff m' evs Hs _. exact (Hsound eff m' evs Hs).
  - intros eff m' evs Hs. destruct (Hsound eff m' evs Hs) as (j & _ & -> & _). apply HhM.
Qed.

End WithSegsCfg.

(** [RealizesCfg.rzc_isteps] over [rzb]. *)
Lemma rzb_isteps : forall segs cfg ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  isteps segs ms ms' ->
  rzb segs cfg (mkCfg ms' model) T ->
  rzb segs cfg (mkCfg ms model) T.
Proof.
  intros segs cfg ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro Hc; [exact Hc|].
  eapply rzb_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

(** [RealizesCfg.rzc_exit] over [rzb]: exit (93) and exit_group (94) are not
    allocation calls. *)
Lemma rzb_exit : forall segs cfg ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  exit_sysno x8 ->
  rzb segs cfg (mkCfg ms model)
    (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros segs cfg ms model x8 Hh Hsvc Hx8. unfold t_exit.
  eapply rzb_emit1; [apply (node_exit_cfg segs cfg ms model x8 Hh Hsvc Hx8) | exact (RomBase.sys_rob_exit segs ms model x8 Hsvc Hx8) | |].
  - apply (nonalloc_sys segs ms model x8 Hsvc).
    change (in_sysno (sys_input segs ms x8)) with x8.
    unfold exit_sysno in Hx8. unfold alloc_mark_sysnos. cbn [In]. lia.
  - apply rzb_halt. cbn [cfg_model]. rewrite m_halted_with_halted. discriminate.
Qed.

(** ** The walk over the binary's own segments, lifted to the run

    LPS 08b1429: [Run.run_scfg_budget_refused] reads the run against
    [run_segments segs inp sp mbase] (the binary's segments with the run's vDSO pair appended)
    and from the start configuration over that list.  A walk is built over the binary's own
    segments, so it is lifted as [RomStable.run_init] lifts a [realizes_cfg] walk: these are
    that file's three theorems over [rzb].  Every node-level step is RomStable's own; the only
    new part is that [nonalloc], which reads the pending number and [sys_input]'s number only,
    is untouched by a change of the read-only backing or of the segment list. *)

Lemma nonalloc_cwrom : forall segs c r, nonalloc segs c -> nonalloc segs (RomBase.cwrom c r).
Proof.
  intros segs [ms model] r H x8 Hx. unfold RomBase.cwrom in *. cbn [cfg_ms] in *.
  change (in_sysno (sys_input segs (RomBase.wrom ms r) x8)) with x8.
  pose proof (H x8 Hx) as H'. cbn [cfg_ms] in H'. change (in_sysno (sys_input segs ms x8)) with x8 in H'.
  exact H'.
Qed.

Lemma nonalloc_app : forall segs tail c, nonalloc segs c -> nonalloc (segs ++ tail) c.
Proof.
  intros segs tail [ms model] H x8 Hx. cbn [cfg_ms] in *.
  change (in_sysno (sys_input (segs ++ tail) ms x8)) with x8.
  pose proof (H x8 Hx) as H'. change (in_sysno (sys_input segs ms x8)) with x8 in H'.
  exact H'.
Qed.

Section RzbWrom.
  Variable segs : list Segment.
  Variable cfg : SpuriousCfg.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_wrom : forall c T, rzb segs cfg c T ->
    forall r, RomBase.rom_ext (ms_rom (cfg_ms c)) r -> rzb segs cfg (RomBase.cwrom c r) T.
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq];
    intros r Hr.
    - apply (rzb_node segs cfg (RomBase.cwrom c r) I evs (fun i => RomBase.cwrom (nx i) r) T i0).
      + eapply RomStable.node_wrom; eassumption.
      + eapply RomStable.sys_rob_wrom; eassumption.
      + apply nonalloc_cwrom; exact Hb.
      + intros i. apply IH.
        match goal with |- RomBase.rom_ext ?x _ => replace x with (ms_rom (cfg_ms c)) end;
          [exact Hr|].
        symmetry. eapply RomStable.node_rom; eassumption.
    - apply rzb_halt. exact Hh.
    - eapply rzb_conseq; [apply IH; exact Hr | exact Heq].
  Qed.
End RzbWrom.

Section RzbAppTail.
  Variables segs tail : list Segment.
  Variable cfg : SpuriousCfg.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_app_tail : forall c T, rzb segs cfg c T -> rzb (segs ++ tail) cfg c T.
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq].
    - apply (rzb_node (segs ++ tail) cfg c I evs nx T i0).
      + eapply RomStable.node_ok_app_tail; eassumption.
      + eapply RomStable.sys_rob_app_tail; eassumption.
      + apply nonalloc_app; exact Hb.
      + exact IH.
    - apply rzb_halt. exact Hh.
    - eapply rzb_conseq; [exact IH | exact Heq].
  Qed.
End RzbAppTail.

Theorem rzb_run_segments : forall segs cfg inp (sp mb : word) c T,
  vdso_image segs = None ->
  rzb segs cfg c T -> rzb (run_segments segs inp sp mb) cfg c T.
Proof.
  intros segs cfg inp sp mb c T Hvi H. unfold run_segments.
  apply (rzb_app_tail segs _ cfg
           (fun s Hs => RomStable.vdso_segments_nx _ _ _ s Hs)
           (fun s Hs => RomStable.vdso_segments_nw _ _ _ s Hs) Hvi).
  exact H.
Qed.

(** A walk over the binary's own segments, from the binary's start, is a walk of the run's
    start over the run's segment list. *)
Theorem rzb_run_init : forall segs cfg inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  rzb segs cfg (init_config segs pc ph sp brk mb rnd lim inp) T ->
  rzb (run_segments segs inp sp mb) cfg
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs cfg inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite RomStable.init_config_run_segments.
  apply rzb_run_segments; [exact Hvi|].
  apply (rzb_wrom segs cfg Hvi); [exact H|].
  rewrite RomStable.init_config_rom. apply RomStable.rom_ext_run_segments.
Qed.

(** [RomStable.realizes_cfg_lift_run] over [rzb]. *)
Theorem rzb_lift_run : forall segs cfg inp (sp mb : word) ms model T,
  vdso_image segs = None -> ms_rom ms = RomStable.seg_rom1 segs ->
  rzb segs cfg (mkCfg ms model) T ->
  rzb (run_segments segs inp sp mb) cfg
    (mkCfg (RomBase.wrom ms (RomStable.seg_rom1 (run_segments segs inp sp mb))) model) T.
Proof.
  intros segs cfg inp sp mb ms model T Hvi Hr H.
  apply rzb_run_segments; [exact Hvi|].
  change (mkCfg (RomBase.wrom ms (RomStable.seg_rom1 (run_segments segs inp sp mb))) model)
    with (RomBase.cwrom (mkCfg ms model) (RomStable.seg_rom1 (run_segments segs inp sp mb))).
  apply (rzb_wrom segs cfg Hvi); [exact H|].
  cbn [cfg_ms]. rewrite Hr. apply RomStable.rom_ext_run_segments.
Qed.

(** ** Soundness *)
Section s.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
(** The filter turns off at most the four allocation numbers. *)
Hypothesis HOFF : forall no, injected_family_off_no cfg no = true -> In no alloc_mark_sysnos.

Lemma unfiltered_of_nonalloc : forall c, nonalloc segs c -> svc_unfiltered segs cfg c.
Proof.
  intros [ms model] Hn x8 Hx. cbn [cfg_ms] in Hx |- *.
  rewrite injected_family_off_sys_input.
  destruct (injected_family_off_no cfg (bv_unsigned x8)) eqn:E; [| reflexivity].
  exfalso. exact (Hn x8 Hx (HOFF _ E)).
Qed.

Lemma sstep_running_b : forall c e st, sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H. destruct H; cbn [cfg_model]; assumption. Qed.

Lemma star_cases_b : forall c tr c', star segs c tr c' ->
  c' = c \/ exists e c2 tr2, sstep segs c e (SNext c2) /\ star segs c2 tr2 c'.
Proof.
  intros c tr c' H. destruct H as [c0 | c1 e c2 tr2 c3 Hss Hstar].
  - left. reflexivity.
  - right. exists e, c2, tr2. split; [exact Hss | exact Hstar].
Qed.

(** Every running configuration the unfiltered run reaches from an [rzb]
    configuration has no unfiltered error step and no allocation call
    pending. *)
Lemma rzb_star_safe : forall c T, rzb segs cfg c T ->
  forall tr c', star segs c tr c' -> m_halted (cfg_model c') = None ->
  (forall e, ~ sstep segs c' e SError) /\ nonalloc segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hrob Hn Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar Hrun.
  - pose proof (unfiltered_of_nonalloc c Hn) as Hu.
    destruct (star_cases_b _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + split; [| exact Hn].
      intros e Hs.
      destruct (proj2 Hnode e SError (sstep_cfg_of_sstep segs cfg c e SError Hu Hs)) as (i & _ & Hbad).
      discriminate Hbad.
    + destruct (proj2 Hnode e (SNext c2) (sstep_cfg_of_sstep segs cfg c e (SNext c2) Hu Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2 Hrun).
  - destruct (star_cases_b _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exfalso. exact (Hh Hrun).
    + exfalso. exact (Hh (sstep_running_b c e _ Hss)).
  - exact (IH tr c' Hstar Hrun).
Qed.

(** A configuration with no unfiltered error step and no allocation call
    pending is not budget-refused. *)
Lemma not_refused_of_safe : forall c,
  (forall e, ~ sstep segs c e SError) -> nonalloc segs c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] Herr Hn [Hh Hb].
  cbn [cfg_ms cfg_model] in Hh, Hb.
  destruct Hb as [(Hsvc & [ (report & Hstep & Hmat)
                          | (Hacct & fn & n & eff & model' & evs' &
                             Hfn & Hsys & Hspec & Hef & Hh' & Hmat) ])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr [] (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr [] (budget_fault_vdso_sstep_error segs ms model fn n eff model' evs'
                      Hh Hsvc Hacct Hfn Hsys Hspec Hef Hh' Hmat)).
  - rewrite (grant_of_nonalloc segs ms model x8 Hn Hx8) in Hgr. discriminate Hgr.
  - exact (Herr [] (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

(** No configuration the unfiltered run reaches from an [rzb] configuration
    is budget-refused. *)
Theorem rzb_never_refused : forall c T, rzb segs cfg c T ->
  ~ reaches_budget_refused segs c.
Proof.
  intros c T H (tr & c' & Hstar & Hb).
  destruct (rzb_star_safe c T H tr c' Hstar (proj1 Hb)) as [Herr Hn].
  exact (not_refused_of_safe c' Herr Hn Hb).
Qed.

(** ... and so under every spurious-failure configuration
    ([Run.reaches_budget_refused_cfg_sub]). *)
Theorem rzb_never_refused_cfg : forall cfg' c T, rzb segs cfg c T ->
  ~ reaches_budget_refused_cfg segs cfg' c.
Proof.
  intros cfg' c T H Hr.
  exact (rzb_never_refused c T H (reaches_budget_refused_cfg_sub segs cfg' c Hr)).
Qed.
End s.

(** [alloc_only_cfg false] turns off only the five allocation numbers. *)
Lemma alloc_only_off : forall no,
  injected_family_off_no (alloc_only_cfg false) no = true -> In no alloc_mark_sysnos.
Proof.
  intros no H. unfold alloc_mark_sysnos. cbn [In].
  destruct (alloc_only_false_off_no no H) as [-> | [-> | [-> | [-> | ->]]]];
    [left | right; left | right; right; left | right; right; right; left
    | right; right; right; right; left]; reflexivity.
Qed.
