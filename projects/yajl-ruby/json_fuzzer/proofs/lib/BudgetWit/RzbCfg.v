(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Common/ShapeAlgCfg.v: the relation realizes_cfg with a grant check and an unfiltered-step check at each node (rzb_cfg), its soundness for the budget premise, and the node lemmas the usage path needs, restated over rzb_cfg. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (budget_refused_at's vDSO materialization fault as a second instruction clause, an SError step by budget_fault_vdso_sstep_error; each rzb_cfg node also asks RomBase.sys_rob, and rzb_never_refused_run lifts a derivation over the binary's own segments to the run's start over run_segments, as RomStable.run_init lifts realizes_cfg). *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import LiaTuning.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Exec RegsEquiv.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common.Cfg Require Import RomBase RomStable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(** * [rzb_cfg]: [ShapeAlgCfg.realizes_cfg] with a grant check and an unfiltered-step check

    [ShapeAlgCfg.realizes_cfg cfg segs c T] ties a trace set to the one-step
    families of the configurations the run FILTERED by [cfg] reaches: its node
    constructor asks for [node_ok_cfg], whose completeness half ranges over
    [sstep_cfg segs cfg].  It has no cut, but a derivation records nothing about
    the configurations it passes, so no [realizes_cfg] proof says that a run is
    never refused by the budget.

    [rzb_cfg cfg segs] has the same three constructors; its node constructor asks,
    besides [node_ok_cfg cfg segs], for two facts about the node's configuration:

    - [grant_ok segs c]: if a syscall is pending, the budget mark
      [Run.alloc_budget_refused_b] answers [false] on it;
    - [unfiltered cfg segs c]: every unfiltered step from [c] is a step of the
      run filtered by [cfg] ([sstep segs] is contained in [sstep_cfg segs cfg]
      at [c]).

    The index [cfg] does not give the premise for free.  The budget premise
    quantifies over every spurious-failure configuration, and the tree's
    derivations are at [alloc_only_cfg false], a filter: its run reaches FEWER
    configurations than the unfiltered run ([Run.star_cfg_sub]), so a fact about
    the filtered run's configurations says nothing about the configurations
    another configuration's run reaches.  The second check closes that gap
    node by node: with it, every unfiltered step from a node is a filtered step,
    so node completeness covers it, and [rzb_star_safe] follows the UNFILTERED
    run.  [rzb_never_refused] is then [~ Run.reaches_budget_refused], and
    [rzb_never_refused_cfg] gives every configuration through
    [Run.reaches_budget_refused_cfg_sub], exactly as at [MayFail] in a
    configuration-free carrier.

    The two first-touch clauses of [Run.budget_refused_at] are premises of an
    unfiltered [SError] step ([Run.budget_fault_instr_sstep_error],
    [Run.budget_fault_syscall_sstep_error]), which node completeness excludes
    through the second check; the grant clause is the negation of [grant_ok].
    [rzb_never_refused_eqv] carries the result across [RegsEquiv.cfg_eqv], since
    the tree's walks start from [RunInit.ms0], a register-map representation of
    the run's initial state, not the state itself. *)

Section g.
Variable segs : list Segment.

(** If a syscall is pending at [c], the budget does not refuse it as a grant. *)
Definition grant_ok (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = false.

Lemma grant_ok_instr : forall ms model,
  ms_svc_pending ms = None -> grant_ok (mkCfg ms model).
Proof.
  intros ms model Hsvc x8 Hx. cbn [cfg_ms] in Hx. rewrite Hsvc in Hx. discriminate Hx.
Qed.
End g.

Section u.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

(** Every unfiltered step from [c] is a step of the run filtered by [cfg]. *)
Definition unfiltered (c : config) : Prop :=
  forall e st, sstep segs c e st -> sstep_cfg segs cfg c e st.

Lemma unfiltered_instr : forall ms model,
  ms_svc_pending ms = None -> unfiltered (mkCfg ms model).
Proof.
  intros ms model Hsvc e st Hs. exact (sstep_cfg_of_sstep_instr cfg segs ms model e st Hsvc Hs).
Qed.

Inductive rzb_cfg : config -> TSet -> Prop :=
| rzb_node_cfg : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok_cfg cfg segs c I evs nx ->
    grant_ok segs c ->
    unfiltered c ->
    sys_rob segs c ->
    (forall i, rzb_cfg (nx i) (T i)) ->
    rzb_cfg c (t_alt (fun i => t_emit (evs i) (T i)))
| rzb_halt_cfg : forall c,
    m_halted (cfg_model c) <> None ->
    rzb_cfg c t_nil
| rzb_conseq_cfg : forall c T T',
    rzb_cfg c T -> t_eq T T' -> rzb_cfg c T'.
End u.

(** ** Soundness *)
Section s.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

Lemma sstep_running_b : forall c e st, sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H. destruct H; cbn [cfg_model]; assumption. Qed.

Lemma star_cases_b : forall c tr c', star segs c tr c' ->
  c' = c \/ exists e c2 tr2, sstep segs c e (SNext c2) /\ star segs c2 tr2 c'.
Proof.
  intros c tr c' H. destruct H as [c0 | c1 e c2 tr2 c3 Hss Hstar].
  - left. reflexivity.
  - right. exists e, c2, tr2. split; [exact Hss | exact Hstar].
Qed.

(** Every running configuration the unfiltered run reaches from an [rzb_cfg]
    configuration has no unfiltered error step and passes the grant check. *)
Lemma rzb_star_safe : forall c T, rzb_cfg cfg segs c T ->
  forall tr c', star segs c tr c' -> m_halted (cfg_model c') = None ->
  (forall e, ~ sstep segs c' e SError) /\ grant_ok segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hg Hu Hrob Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar Hrun.
  - destruct (star_cases_b _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + split; [| exact Hg].
      intros e Hs. destruct (proj2 Hnode e SError (Hu e SError Hs)) as (i & _ & Hbad).
      discriminate Hbad.
    + destruct (proj2 Hnode e (SNext c2) (Hu e (SNext c2) Hss)) as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2 Hrun).
  - destruct (star_cases_b _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exfalso. exact (Hh Hrun).
    + exfalso. exact (Hh (sstep_running_b c e _ Hss)).
  - exact (IH tr c' Hstar Hrun).
Qed.

(** A configuration with no unfiltered error step that passes the grant check
    is not budget-refused. *)
Lemma not_refused_of_safe : forall c,
  (forall e, ~ sstep segs c e SError) -> grant_ok segs c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] Herr Hg [Hh Hb].
  cbn [cfg_ms cfg_model] in Hh, Hb.
  (* LPS 727298f3: [Run.budget_refused_at]'s instruction half is two clauses -- the
     first-touch fault and the vDSO materialization fault -- and both are premises of an
     [SError] step ([Run.budget_fault_instr_sstep_error], [Run.budget_fault_vdso_sstep_error]). *)
  destruct Hb as [(Hsvc & [ (report & Hstep & Hmat)
                          | (Hacct & fn & n & eff0 & model0 & evs0 & Hfn & Hsys & Hspec0 & Hret0 & Hh0 & Hmat0) ])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr [] (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr [] (budget_fault_vdso_sstep_error segs ms model fn n eff0 model0 evs0
                     Hh Hsvc Hacct Hfn Hsys Hspec0 Hret0 Hh0 Hmat0)).
  - pose proof (Hg x8 Hx8) as Hg'. cbn [cfg_ms cfg_model] in Hg'. congruence.
  - exact (Herr [] (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

(** ... and neither is any configuration equivalent to it. *)
Lemma not_refused_of_safe_eqv : forall c c', cfg_eqv c c' ->
  (forall e, ~ sstep segs c' e SError) -> grant_ok segs c' -> ~ budget_refused_at segs c.
Proof.
  intros [ms mo] [ms' mo'] [Hms Hmo] Herr Hg [Hh Hb].
  cbn [cfg_ms cfg_model] in Hms, Hmo, Hh, Hb. subst mo'.
  pose proof Hms as (_ & _ & _ & Hsvc' & _).
  assert (Hno : ~ sstep segs (mkCfg ms mo) [] SError).
  { intros Hs. destruct (sstep_eqv segs ms ms' mo [] SError Hms Hs) as (X' & Hs' & HX).
    destruct X'; cbn [to_eqv] in HX; first [contradiction | exact (Herr [] Hs')]. }
  destruct Hb as [(Hsvc & [ (report & Hstep & Hmat)
                          | (Hacct & fn & n & eff0 & model0 & evs0 & Hfn & Hsys & Hspec0 & Hret0 & Hh0 & Hmat0) ])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Hno (budget_fault_instr_sstep_error segs ms mo report Hh Hsvc Hstep Hmat)).
  - exact (Hno (budget_fault_vdso_sstep_error segs ms mo fn n eff0 model0 evs0
                 Hh Hsvc Hacct Hfn Hsys Hspec0 Hret0 Hh0 Hmat0)).
  - assert (Hx8' : ms_svc_pending ms' = Some x8) by congruence.
    pose proof (Hg x8 Hx8') as Hg'. cbn [cfg_ms cfg_model] in Hg'.
    rewrite <- (sys_input_eqv segs ms ms' x8 Hms) in Hg'. congruence.
  - exact (Hno (budget_fault_syscall_sstep_error segs ms mo x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

(** No configuration the unfiltered run reaches from an [rzb_cfg] configuration
    is budget-refused. *)
Theorem rzb_never_refused : forall c T, rzb_cfg cfg segs c T ->
  ~ reaches_budget_refused segs c.
Proof.
  intros c T H (tr & c' & Hstar & Hb).
  destruct (rzb_star_safe c T H tr c' Hstar (proj1 Hb)) as [Herr Hg].
  exact (not_refused_of_safe c' Herr Hg Hb).
Qed.

(** ... and so under every spurious-failure configuration
    ([Run.reaches_budget_refused_cfg_sub]). *)
Theorem rzb_never_refused_cfg : forall cfg' c T, rzb_cfg cfg segs c T ->
  ~ reaches_budget_refused_cfg segs cfg' c.
Proof.
  intros cfg' c T H Hr. exact (rzb_never_refused c T H (reaches_budget_refused_cfg_sub segs cfg' c Hr)).
Qed.

(** The same from a configuration equivalent to the derivation's
    ([RegsEquiv.star_eqv] follows the run across [cfg_eqv]). *)
Theorem rzb_never_refused_eqv : forall c0 c T, cfg_eqv c0 c -> rzb_cfg cfg segs c T ->
  ~ reaches_budget_refused segs c0.
Proof.
  intros c0 c T Heqv H (tr & c1 & Hstar & Hb).
  destruct (star_eqv segs c0 tr c1 Hstar c Heqv) as (c1' & Hstar' & Heqv1).
  assert (Hrun : m_halted (cfg_model c1') = None).
  { destruct Heqv1 as [_ Hmo]. rewrite <- Hmo. exact (proj1 Hb). }
  destruct (rzb_star_safe c T H tr c1' Hstar' Hrun) as [Herr Hg].
  exact (not_refused_of_safe_eqv c1 c1' Heqv1 Herr Hg Hb).
Qed.
End s.

(** ** Node lemmas over [rzb_cfg] *)
Section d2.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

Lemma rzb_nonempty : forall c T, rzb_cfg cfg segs c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hg Hu Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma rzb_silent1_cfg : forall c c' T,
  node_ok_cfg cfg segs c unit (fun _ => []) (fun _ => c') ->
  grant_ok segs c -> unfiltered cfg segs c -> sys_rob segs c ->
  rzb_cfg cfg segs c' T ->
  rzb_cfg cfg segs c T.
Proof.
  intros c c' T Hnode Hg Hu Hrob Hc.
  apply (rzb_conseq_cfg cfg segs c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzb_node_cfg cfg segs c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hg Hu Hrob).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply rzb_nonempty; exact Hc ].
Qed.

Lemma rzb_step_cfg : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  rzb_cfg cfg segs (mkCfg ms' model) T ->
  rzb_cfg cfg segs (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rzb_silent1_cfg;
    [ apply (node_instr_cfg cfg segs ms model ms' Hh Hlazy Hsvc Hstep)
    | apply grant_ok_instr; exact Hsvc
    | apply unfiltered_instr; exact Hsvc
    | apply sys_rob_instr; exact Hsvc
    | exact Hc ].
Qed.

Lemma rzb_msteps_lib_cfg : forall ms ms' mo T,
  m_halted mo = None -> m_vm_lazy mo = [] ->
  Exec.msteps segs ms ms' ->
  rzb_cfg cfg segs (mkCfg ms' mo) T -> rzb_cfg cfg segs (mkCfg ms mo) T.
Proof.
  intros ms ms' mo T Hh Hl Hms. induction Hms as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH]; intros Hc.
  - exact Hc.
  - eapply rzb_step_cfg; [exact Hh | exact Hl | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.
End d2.

(** ** The run's start (LPS 08b1429)

    The run reads the binary against [run_segments segs inp sp mb], the binary's segments with
    the vDSO pair appended, from [init_config (run_segments ..) ..], whose read-only backing
    also reads the pair ([RomStable.init_config_run_segments]).  [rzb_cfg_wrom] and
    [rzb_cfg_app_tail] carry a derivation over the binary's own segments there, as
    [RomStable.realizes_cfg_wrom] and [RomStable.realizes_cfg_app_tail] do for
    [realizes_cfg] (whose node checks are [rzb_cfg]'s first and fourth).  The unfiltered-step
    check goes across through [Run.sstep_cfg_may_fail]: an unfiltered step is a step at
    [may_fail_cfg], which RomStable's backward lemmas map to a step of the original
    configuration, and node completeness makes that a step to a successor, which RomStable's
    forward lemmas map back.  The grant check goes across because
    [Run.alloc_budget_refused_b] reads only the call's number and arguments.
    [rzb_never_refused_run] is [rzb_never_refused_eqv] at the run's own start, the
    configuration [Run.run_budget_refused] reads. *)

Lemma alloc_budget_refused_b_wrom : forall segs ms r x8 m,
  alloc_budget_refused_b (sys_input segs (wrom ms r) x8) m = alloc_budget_refused_b (sys_input segs ms x8) m.
Proof. intros segs ms r x8 m. reflexivity. Qed.

Section RunWrom.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Hypothesis Hvi : vdso_image segs = None.

Lemma grant_ok_wrom : forall c r, grant_ok segs c -> grant_ok segs (cwrom c r).
Proof.
  intros [ms mo] r Hg x8 Hx8. unfold cwrom in *. cbn [cfg_ms cfg_model] in *.
  rewrite alloc_budget_refused_b_wrom. exact (Hg x8 Hx8).
Qed.

Lemma unfiltered_wrom : forall c I evs nx r,
  node_ok_cfg cfg segs c I evs nx -> sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r ->
  unfiltered cfg segs c -> unfiltered cfg segs (cwrom c r).
Proof.
  intros c I evs nx r [_ Hs] Hrob Hr Hu e st Hst.
  apply (proj1 (sstep_cfg_may_fail segs _ _ _)) in Hst.
  destruct (sstep_wrom_back segs may_fail_cfg Hvi c e st r Hrob Hr Hst) as (st0 & H0 & ->).
  pose proof (Hu e st0 (proj2 (sstep_cfg_may_fail segs _ _ _) H0)) as H1.
  destruct (Hs e st0 H1) as (i & _ & ->).
  exact (sstep_wrom_fwd segs cfg Hvi c e (nx i) r Hrob Hr H1).
Qed.

Theorem rzb_cfg_wrom : forall c T, rzb_cfg cfg segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> rzb_cfg cfg segs (cwrom c r) T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hg Hu Hrob Hc IH | c Hh | c T T' H IH Heq]; intros r Hr.
  - apply (rzb_node_cfg cfg segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (node_wrom segs cfg Hvi c I evs nx r Hn Hrob Hr).
    + exact (grant_ok_wrom c r Hg).
    + exact (unfiltered_wrom c I evs nx r Hn Hrob Hr Hu).
    + exact (sys_rob_wrom segs c r Hrob Hr).
    + intros i. apply IH. rewrite (node_rom segs cfg Hvi c I evs nx Hn i). exact Hr.
  - apply rzb_halt_cfg. exact Hh.
  - eapply rzb_conseq_cfg; [apply IH; exact Hr | exact Heq].
Qed.
End RunWrom.

Section RunAppTail.
Variables segs tail : list Segment.
Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
Hypothesis Hvi : vdso_image segs = None.
Variable cfg : SpuriousCfg.

Lemma grant_ok_app_tail : forall c, grant_ok segs c -> grant_ok (segs ++ tail) c.
Proof.
  intros c Hg x8 Hx8. rewrite sys_input_app_nw by assumption. exact (Hg x8 Hx8).
Qed.

Lemma unfiltered_app_tail : forall c I evs nx (i0 : I),
  node_ok_cfg cfg segs c I evs nx -> unfiltered cfg segs c -> unfiltered cfg (segs ++ tail) c.
Proof.
  intros [ms model] I evs nx i0 [Hc Hs] Hu e st Hst.
  assert (Hok : ms_svc_pending ms = None -> exists r, mi_account_step segs ms model = MachineOk r).
  { intros Hsvc. pose proof (Hc i0) as H0. inversion H0; subst.
    - eexists. eassumption.
    - exfalso. rewrite (vdso_entry_fn_none_seg segs Hvi) in *. discriminate.
    - congruence.
    - congruence.
    - congruence. }
  apply (proj1 (sstep_cfg_may_fail (segs ++ tail) _ _ _)) in Hst.
  assert (Hb : sstep_cfg segs may_fail_cfg (mkCfg ms model) e st)
    by (apply (sstep_cfg_app_back segs tail); assumption).
  pose proof (Hu e st (proj2 (sstep_cfg_may_fail segs _ _ _) Hb)) as H1.
  destruct (Hs e st H1) as (i & _ & ->).
  apply (sstep_cfg_app_next segs tail); assumption.
Qed.

Theorem rzb_cfg_app_tail : forall c T, rzb_cfg cfg segs c T -> rzb_cfg cfg (segs ++ tail) c T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hg Hu Hrob Hc IH | c Hh | c T T' H IH Heq].
  - apply (rzb_node_cfg cfg (segs ++ tail) c I evs nx T i0).
    + apply (node_ok_app_tail segs tail); assumption.
    + exact (grant_ok_app_tail c Hg).
    + exact (unfiltered_app_tail c I evs nx i0 Hn Hu).
    + apply (sys_rob_app_tail segs tail); assumption.
    + exact IH.
  - exact (rzb_halt_cfg cfg (segs ++ tail) c Hh).
  - exact (rzb_conseq_cfg cfg (segs ++ tail) c T T' IH Heq).
Qed.
End RunAppTail.

Theorem rzb_cfg_run_segments : forall cfg segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  rzb_cfg cfg segs c T -> rzb_cfg cfg (run_segments segs inp sp mb) c T.
Proof.
  intros cfg segs inp sp mb c T Hvi H. unfold run_segments.
  apply rzb_cfg_app_tail;
    [ intros s Hs; exact (vdso_segments_nx _ _ _ s Hs)
    | intros s Hs; exact (vdso_segments_nw _ _ _ s Hs)
    | exact Hvi | exact H ].
Qed.

Lemma cfg_eqv_wrom : forall c c' r, cfg_eqv c c' -> cfg_eqv (cwrom c r) (cwrom c' r).
Proof.
  intros c c' r [(H1 & H2 & H3 & H4 & H5 & H6 & H7 & _) Hm].
  exact (conj (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 eq_refl))))))) Hm).
Qed.

(** A derivation over the binary's own segments from a configuration equivalent to the
    binary's start: the run, from its own start, reaches no budget-refused configuration. *)
Theorem rzb_never_refused_run : forall cfg segs inp (sp mb : word) pc ph brk rnd lim c T,
  vdso_image segs = None ->
  cfg_eqv (init_config segs pc ph sp brk mb rnd lim inp) c ->
  rzb_cfg cfg segs c T ->
  ~ reaches_budget_refused (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp).
Proof.
  intros cfg segs inp sp mb pc ph brk rnd lim c T Hvi E H.
  assert (Hr : rom_ext (ms_rom (cfg_ms c)) (seg_rom1 (run_segments segs inp sp mb))).
  { destruct E as [(_ & _ & _ & _ & _ & _ & _ & Hrom) _].
    rewrite <- Hrom, init_config_rom. apply rom_ext_run_segments. }
  rewrite init_config_run_segments.
  exact (rzb_never_refused_eqv cfg (run_segments segs inp sp mb) _ _ T
           (cfg_eqv_wrom _ _ (seg_rom1 (run_segments segs inp sp mb)) E)
           (rzb_cfg_run_segments cfg segs inp sp mb _ T Hvi (rzb_cfg_wrom cfg segs Hvi c T H _ Hr))).
Qed.
