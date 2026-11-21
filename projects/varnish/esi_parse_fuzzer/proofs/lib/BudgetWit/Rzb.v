(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from ShapeAlg.v: the relation realizes0 with a no-allocation check at each node (rzb), its soundness for the budget premise, and the node lemmas restated over rzb. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: budget_refused_at's no-syscall half is a disjunction, and a walk over the binary's own segments lifts to the run's segment list from the run's start (rzb_run_segments, rzb_run_init). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim MmapSim AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RomBase RomStable.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg.Allo9zm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
Import ListNotations.
Open Scope bv_scope.

(** * [rzb]: [ShapeAlg.realizes0] with a no-allocation check at each node

    [ShapeAlg.realizes segs c T] is [never_excused segs c -> realizes0 segs c T]
    in a budget world [BWorld.BWorld]: in the world [BWorld.bw_premise lim] the
    walk is proved under the budget premise, which [BWorld.never_excused_of_premise]
    turns into [never_excused] at the start configuration, so a [realizes]
    proof assumes the premise and cannot give it.  [realizes0] has no cut, but
    a derivation records nothing about the configurations it passes.  Its
    [node_ok] is stated over the filtered step [sstep_cfg segs ACFG]
    ([Acfg.ACFG = alloc_only_cfg false]), while the budget premise is shown false
    through the unfiltered [star] ([Run.reaches_budget_refused_cfg_sub]).

    [rzb] has the same three constructors as [realizes0], and its node
    constructor asks, besides [node_ok], for [nonalloc c]: if a syscall is
    pending at [c], its number is none of [Run.alloc_mark_sysnos] (brk 214,
    mremap 216, mmap 222, mprotect 226).  That one fact gives both halves of the
    budget premise at a node:
    - every step of the unfiltered relation [sstep] from [c] is a step of
      [sstep_cfg segs ACFG] ([Acfg.sstep_cfg_of_instr],
      [Acfg.sstep_cfg_of_nonalloc]; [sstep_cfg_of_nonalloc_c] below), so the
      completeness half of [node_ok] covers it, and the first-touch clauses of
      [Run.budget_refused_at], which are premises of an [SError] step
      ([Run.budget_fault_instr_sstep_error],
      [Run.budget_fault_syscall_sstep_error]), cannot hold;
    - the grant clause [Run.alloc_budget_refused_b] answers [false] off the four
      allocation numbers ([Run.alloc_budget_refused_b_outside];
      [nonalloc_grant] below).

    [rzb_never_refused]: no configuration the unfiltered run reaches from an
    [rzb] configuration is budget-refused, and so none the run under any
    spurious-failure configuration reaches ([rzb_never_refused_cfg]).

    The rest of the file is ShapeAlg's lemmas that build a [realizes] node,
    restated over [rzb] with their proofs: [rz_] is written [rzb_].  [rzb] needs
    no budget world: it is [realizes0] plus the check.  A lemma that takes a
    [node_ok] also takes [nonalloc] for the same configuration; a lemma whose
    node is an instruction or an exit derives it. *)

Section WithSegs.
Variable segs : list Segment.

(** If a syscall is pending, it is not one of the four allocation calls. *)
Definition nonalloc (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.

Lemma nonalloc_instr : forall ms model, ms_svc_pending ms = None -> nonalloc (mkCfg ms model).
Proof. intros ms model H x8 Hx. cbn [cfg_ms] in Hx. congruence. Qed.

Lemma nonalloc_no : forall ms model x8,
  ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false -> nonalloc (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hno y Hy. cbn [cfg_ms] in Hy. rewrite Hsvc in Hy.
  injection Hy as <-. exact (alloc_no_b_false _ Hno).
Qed.

(** Off the allocation calls, the unfiltered step is the filtered one. *)
Lemma sstep_cfg_of_nonalloc_c : forall c e st,
  nonalloc c -> sstep segs c e st -> sstep_cfg segs ACFG c e st.
Proof.
  intros [ms model] e st Hna Hs.
  destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - exact (sstep_cfg_of_nonalloc segs ms model x8 e st Hsvc (Hna x8 Hsvc) Hs).
  - exact (sstep_cfg_of_instr segs ms model e st Hsvc Hs).
Qed.

(** Off the allocation calls, the budget refuses no grant. *)
Lemma nonalloc_grant : forall c x8,
  nonalloc c -> ms_svc_pending (cfg_ms c) = Some x8 ->
  alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = false.
Proof.
  intros c x8 Hna Hx. apply alloc_budget_refused_b_outside. exact (Hna x8 Hx).
Qed.

Lemma sstep_halted_none_u : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    nonalloc c ->
    (forall i, rzb (nx i) (T i)) ->
    rzb c (t_alt (fun i => t_emit (evs i) (T i)))
| rzb_halt : forall c,
    m_halted (cfg_model c) <> None ->
    rzb c t_nil
| rzb_conseq : forall c T T',
    rzb c T -> t_eq T T' -> rzb c T'.

(** ** Soundness for the budget premise *)

Lemma star_cases : forall c tr c', star segs c tr c' ->
  c' = c \/ exists e c2 tr2, sstep segs c e (SNext c2) /\ star segs c2 tr2 c'.
Proof.
  intros c tr c' H. destruct H as [c0 | c1 e c2 tr2 c3 Hss Hstar].
  - left. reflexivity.
  - right. exists e, c2, tr2. split; [exact Hss | exact Hstar].
Qed.

(** A node with the check is not budget-refused. *)
Lemma node_not_refused : forall c I evs nx,
  node_ok segs c I evs nx -> nonalloc c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ [Hc _]] Hna [Hh Hr].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs.
    destruct (Hc [] SError (sstep_cfg_of_nonalloc_c _ [] SError Hna Hs)) as (i & _ & Hbad).
    discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hr.
  (* [Run.budget_refused_at]'s no-syscall half is a disjunction now: the
     first-touch instruction fault and the vDSO materialization fault.  Both
     are premises of an [SError] step, so both close the same way. *)
  destruct Hr as [(Hsvc & [ (report & Hstep & Hmat)
                          | (Hacct & fn & n & eff & model' & evs' &
                             Hfn & Hsys & Hspec & Hef & Hh' & Hmat) ])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr (budget_fault_vdso_sstep_error segs ms model fn n eff model' evs'
                   Hh Hsvc Hacct Hfn Hsys Hspec Hef Hh' Hmat)).
  - pose proof (nonalloc_grant (mkCfg ms model) x8 Hna Hx8) as Hg.
    cbn [cfg_ms cfg_model] in Hg. congruence.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma rzb_star_not_refused : forall c T, rzb c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hna Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hna).
    + destruct (proj1 (proj2 Hnode) e (SNext c2) (sstep_cfg_of_nonalloc_c c e (SNext c2) Hna Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + intros [Hn _]. exact (Hh Hn).
    + exfalso. exact (Hh (sstep_halted_none_u c e _ Hss)).
  - exact (IH tr c' Hstar).
Qed.

(** No configuration the unfiltered run reaches from an [rzb] configuration is
    budget-refused. *)
Theorem rzb_never_refused : forall c T, rzb c T -> ~ reaches_budget_refused segs c.
Proof.
  intros c T H (tr & c' & Hstar & Hb). exact (rzb_star_not_refused c T H tr c' Hstar Hb).
Qed.

(** ...and so under every spurious-failure configuration
    ([Run.reaches_budget_refused_cfg_sub]). *)
Theorem rzb_never_refused_cfg : forall cfg c T, rzb c T ->
  ~ reaches_budget_refused_cfg segs cfg c.
Proof.
  intros cfg c T H Hr. exact (rzb_never_refused c T H (reaches_budget_refused_cfg_sub segs cfg c Hr)).
Qed.

(** ** ShapeAlg's node lemmas over [rzb] *)

Lemma rzb_nonempty : forall c T, rzb c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hna Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma rzb_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  nonalloc c ->
  rzb c' T ->
  rzb c T.
Proof.
  intros c c' T Hnode Hna Hc.
  apply (rzb_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzb_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hna).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply rzb_nonempty; exact Hc ].
Qed.

Lemma rzb_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  nonalloc c ->
  rzb c' T ->
  rzb c (t_emit e T).
Proof.
  intros c c' e T Hnode Hna Hc.
  apply (rzb_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rzb_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hna).
    intros []; exact Hc.
  - apply t_alt_unit.
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
  eapply rzb_silent1; [apply node_instr; eassumption | apply nonalloc_instr; exact Hsvc | exact Hc].
Qed.

Lemma rzb_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  rzb (mkCfg ms' model) T ->
  rzb (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rzb_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                   | apply IH; exact Hc].
Qed.

Lemma rzb_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  rzb (mkCfg ms model)
      (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  assert (Hna : nonalloc (mkCfg ms model)).
  { apply (nonalloc_no ms model x8 Hsvc).
    destruct Hx8 as [E | E]; rewrite E; reflexivity. }
  unfold t_exit.
  eapply (rzb_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - split; [| split].
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_cfg_exit segs ACFG ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 (sstep_cfg_sub segs ACFG _ _ _ Hss)) as [-> ->].
      exists tt. split; reflexivity.
    + exact (RomBase.sys_rob_exit segs ms model x8 Hsvc Hx8).
  - exact Hna.
  - apply rzb_halt. cbn. discriminate.
Qed.

End WithSegs.

(** ** The walk over the binary's own segments, lifted to the run

    At LPS 727298f3 [Run.run_scfg_budget_refused] reads the run against
    [run_segments segs inp sp mbase] (the binary's segments with the run's vDSO
    pair appended) and from the start configuration over that list.  An [rzb]
    walk is built over the binary's own segments, so it is lifted exactly as
    [RomStable.run_init0] lifts a [ShapeAlg.realizes0] walk: [node_ok] carries
    over by [RomStable.node_wrom] and [RomStable.node_ok_app_tail], and
    [nonalloc], which reads [ms_svc_pending] alone, is untouched by a change of
    the read-only backing.  The three theorems are bzip2/bzip2_compress_target's
    [Rzb.rzb_wrom], [Rzb.rzb_app_tail] and [Rzb.rzb_run_init] over this tree's
    [rzb]. *)

Lemma nonalloc_cwrom : forall c r, nonalloc c -> nonalloc (RomBase.cwrom c r).
Proof. intros [ms model] r H. exact H. Qed.

Section RzbWrom.
  Variable segs : list Segment.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_wrom : forall c T, rzb segs c T ->
    forall r, RomBase.rom_ext (ms_rom (cfg_ms c)) r -> rzb segs (RomBase.cwrom c r) T.
  Proof using Hvi.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hb Hc IH | c Hh | c T T' H IH Heq];
    intros r Hr.
    - apply (rzb_node segs (RomBase.cwrom c r) I evs (fun i => RomBase.cwrom (nx i) r) T i0).
      + eapply RomStable.node_wrom; eassumption.
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
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_app_tail : forall c T, rzb segs c T -> rzb (segs ++ tail) c T.
  Proof using Hnx Hnw Hvi.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hb Hc IH | c Hh | c T T' H IH Heq].
    - apply (rzb_node (segs ++ tail) c I evs nx T i0).
      + eapply RomStable.node_ok_app_tail; eassumption.
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
           (fun s Hs => RomStable.vdso_segments_nx _ _ _ s Hs)
           (fun s Hs => RomStable.vdso_segments_nw _ _ _ s Hs) Hvi).
  exact H.
Qed.

(** A walk over the binary's own segments, from the binary's start, is a walk of
    the run's start over the run's segment list. *)
Theorem rzb_run_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  rzb segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  rzb (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite RomStable.init_config_run_segments.
  apply rzb_run_segments; [exact Hvi|].
  apply (rzb_wrom segs Hvi); [exact H|].
  rewrite RomStable.init_config_rom. apply RomStable.rom_ext_run_segments.
Qed.
