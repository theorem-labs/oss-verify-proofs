(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from ShapeAlg.v: the relation realizes with a grant check at each node (rzb), its soundness for the budget premise, and the node lemmas of ShapeAlg.v that the usage walk uses, restated over rzb. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the vDSO arm of the budget refusal; RomBase.sys_rob in the rzb node; the lift of an rzb walk over the binary's own segments to the run's segment list). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SimInv ExitSim CatSim MmapSim AllocSim AllocSim2 WallSim ShapeAlg.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require RomBase RomStable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(** * [rzb]: [ShapeAlg.realizes] with a grant check at each node

    [ShapeAlg.realizes segs c T] ties a trace set to the one-step families
    of the configurations a run reaches.  Its [node_ok] is stated over the
    unfiltered step [sstep], and it has no cut.  But a derivation records
    nothing about the system calls it passes, so no [realizes] proof says
    that a run is never refused by the budget: an mmap or brk emits no
    event, and a node may answer one.  [rzb] has the same three
    constructors, and its node constructor asks, besides [node_ok], for
    [grant_ok segs c]: if a syscall is pending at [c], the budget mark
    [Run.alloc_budget_refused_b] answers [false] on it.

    [rzb_never_refused]: no configuration the unfiltered run reaches from
    an [rzb] configuration is budget-refused.  The two first-touch clauses
    of [Run.budget_refused_at] are premises of an [SError] step
    ([Run.budget_fault_instr_sstep_error],
    [Run.budget_fault_syscall_sstep_error]), which the completeness half of
    [node_ok] excludes; the grant clause is the negation of [grant_ok]; a
    halted configuration is not budget-refused.

    [grant_ok] holds at an instruction ([grant_ok_instr]) and at a syscall
    whose number is none of 214, 216, 222 and 226, the RISC-V Linux numbers
    of brk, mremap, mmap and mprotect ([Run.alloc_mark_sysnos];
    [grant_ok_nonalloc], [grant_ok_num], [grant_ok_exit]).

    The rest of the file is ShapeAlg's lemmas that build a [realizes] node,
    restated over [rzb] with their proofs: [rz_] is written [rzb_].  A
    lemma that takes a [node_ok] also takes [grant_ok] for the same
    configuration; a lemma whose node is an instruction or an exit derives
    it. *)

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

Lemma grant_ok_nonalloc : forall ms model x8,
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  grant_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hn y Hy. cbn [cfg_ms cfg_model] in *. rewrite Hsvc in Hy. injection Hy as <-.
  apply alloc_budget_refused_b_outside. rewrite in_sysno_sys_input. exact Hn.
Qed.

(** The form a node lemma gives: the number as a literal, checked by
    [existsb]. *)
Lemma grant_ok_num : forall ms model x8 n,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n ->
  existsb (Z.eqb n) alloc_mark_sysnos = false ->
  grant_ok (mkCfg ms model).
Proof.
  intros ms model x8 n Hsvc Hx Hb. apply (grant_ok_nonalloc ms model x8 Hsvc).
  rewrite Hx. intros Hin.
  assert (Ht : existsb (Z.eqb n) alloc_mark_sysnos = true).
  { apply existsb_exists. exists n. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

(** The exit (93 or 94) is off the four allocation numbers. *)
Lemma grant_ok_exit : forall ms model x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 -> grant_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc [Hx | Hx];
    exact (grant_ok_num ms model x8 _ Hsvc Hx eq_refl).
Qed.
End g.

Section d.
Variable segs : list Segment.

Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (* LPS 727298f3: the node's system call reads the same over a larger read-only backing, so
       a walk over the binary's own segments lifts to the run's segment list
       ([rzb_run_init]).  [ShapeAlg.rz_node] asks the same, in the same place. *)
    RomBase.sys_rob segs c ->
    grant_ok segs c ->
    (forall i, rzb (nx i) (T i)) ->
    rzb c (t_alt (fun i => t_emit (evs i) (T i)))
| rzb_halt : forall c,
    m_halted (cfg_model c) <> None ->
    rzb c t_nil
| rzb_conseq : forall c T T',
    rzb c T -> t_eq T T' -> rzb c T'.
End d.

(** ** Soundness for the budget premise *)
Section s.
Variable segs : list Segment.

Lemma star_cases : forall c tr c', star segs c tr c' ->
  c' = c \/ exists e c2 tr2, sstep segs c e (SNext c2) /\ star segs c2 tr2 c'.
Proof.
  intros c tr c' H. destruct H as [c0 | c1 e c2 tr2 c3 Hss Hstar].
  - left. reflexivity.
  - right. exists e, c2, tr2. split; [exact Hss | exact Hstar].
Qed.

(** A node with the grant check is not budget-refused. *)
Lemma node_not_refused : forall c I evs nx,
  node_ok segs c I evs nx -> grant_ok segs c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ Hc] Hg [Hh Hr].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs. destruct (Hc [] SError Hs) as (i & _ & Hbad). discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hr.
  (* LPS 727298f3: the instruction half of [Run.budget_refused_at] is two clauses, the
     first-touch fault and the vDSO materialization fault; both are premises of an [SError]
     step ([Run.budget_fault_instr_sstep_error], [Run.budget_fault_vdso_sstep_error]). *)
  destruct Hr as [(Hsvc & [ (report & Hstep & Hmat)
                          | (Hacct & fn & n & eff0 & model0 & evs0 & Hfn & Hsys & Hspec0 & Hret0 & Hh0 & Hmat0) ])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr (budget_fault_vdso_sstep_error segs ms model fn n eff0 model0 evs0
                   Hh Hsvc Hacct Hfn Hsys Hspec0 Hret0 Hh0 Hmat0)).
  - pose proof (Hg x8 Hx8) as Hg'. cbn [cfg_ms cfg_model] in Hg'. congruence.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma rzb_star_not_refused : forall c T, rzb segs c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hrob Hg Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hg).
    + destruct (proj2 Hnode e (SNext c2) Hss) as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + intros [Hn _]. exact (Hh Hn).
    + exfalso. exact (Hh (sstep_halted_none segs c e _ Hss)).
  - exact (IH tr c' Hstar).
Qed.

(** No configuration the unfiltered run reaches from an [rzb]
    configuration is budget-refused. *)
Theorem rzb_never_refused : forall c T, rzb segs c T -> ~ reaches_budget_refused segs c.
Proof.
  intros c T H (tr & c' & Hstar & Hb). exact (rzb_star_not_refused c T H tr c' Hstar Hb).
Qed.

(** ...and so under every spurious-failure configuration
    ([Run.reaches_budget_refused_cfg_sub]). *)
Theorem rzb_never_refused_cfg : forall cfg c T, rzb segs c T ->
  ~ reaches_budget_refused_cfg segs cfg c.
Proof.
  intros cfg c T H Hr. exact (rzb_never_refused c T H (reaches_budget_refused_cfg_sub segs cfg c Hr)).
Qed.
End s.

(** ** ShapeAlg's node lemmas over [rzb] *)
Section WithSegs.
Variable segs : list Segment.

Lemma rzb_nonempty : forall c T, rzb segs c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hg Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma rzb_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  grant_ok segs c ->
  rzb segs c' T ->
  rzb segs c T.
Proof.
  intros c c' T Hnode Hrob Hg Hc.
  apply (rzb_conseq segs c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzb_node segs c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob Hg).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply rzb_nonempty; exact Hc ].
Qed.

Lemma rzb_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  grant_ok segs c ->
  rzb segs c' T ->
  rzb segs c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hg Hc.
  apply (rzb_conseq segs c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rzb_node segs c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob Hg).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

Lemma rzb_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  rzb segs (mkCfg ms' model) T ->
  rzb segs (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rzb_silent1;
    [ apply node_instr; eassumption
    | apply RomBase.sys_rob_instr; cbn [cfg_ms]; exact Hsvc
    | apply grant_ok_instr; exact Hsvc | exact Hc].
Qed.

Lemma rzb_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  rzb segs (mkCfg ms' model) T ->
  rzb segs (mkCfg ms model) T.
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
  rzb segs (mkCfg ms model)
      (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rzb_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - split.
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
  - destruct Hx8 as [Hx8' | Hx8'];
      (eapply RomBase.sys_rob_memfree;
         [exact Hsvc | rewrite Hx8'; first [exact RomBase.memfree_93 | exact RomBase.memfree_94]]).
  - exact (grant_ok_exit segs ms model x8 Hsvc Hx8).
  - apply rzb_halt. cbn. discriminate.
Qed.

End WithSegs.

(** ** The walk over the binary's own segments, lifted to the run

    LPS 727298f3: [Run.run_budget_refused] reads the run against
    [run_segments segs inp sp mbase] -- the binary's segments with the run's vDSO
    appended -- and from the start configuration over that list.  A walk is built
    over the binary's own segments, so it has to be lifted, exactly as
    [RomStable.run_init] lifts a [ShapeAlg.realizes] walk.  These are that file's
    three theorems over [rzb]; every node-level step is RomStable's own, and the
    only new part is that [grant_ok] holds over the larger backing and over the
    longer list: [Run.alloc_budget_refused_b] reads only the number and the
    arguments of the call, which neither changes. *)

Lemma alloc_budget_refused_b_with_mem : forall i mp m,
  alloc_budget_refused_b (RomBase.with_mem i mp) m = alloc_budget_refused_b i m.
Proof. intros i mp m. destruct i. reflexivity. Qed.

Lemma grant_ok_cwrom : forall segs c r, grant_ok segs c -> grant_ok segs (RomBase.cwrom c r).
Proof.
  intros segs [ms model] r H x8 Hx.
  (* [RomBase.sys_input_wrom]: the input over the larger backing is the input with another
     memory view, by conversion *)
  exact (eq_trans (alloc_budget_refused_b_with_mem (sys_input segs ms x8)
                     (ms_read_byte (RomBase.wrom ms r)) model)
                  (H x8 Hx)).
Qed.

Section RzbWrom.
  Variable segs : list Segment.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_wrom : forall c T, rzb segs c T ->
    forall r, RomBase.rom_ext (ms_rom (cfg_ms c)) r -> rzb segs (RomBase.cwrom c r) T.
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hg Hc IH | c Hh | c T T' H IH Heq];
    intros r Hr.
    - apply (rzb_node segs (RomBase.cwrom c r) I evs (fun i => RomBase.cwrom (nx i) r) T i0).
      + eapply RomStable.node_wrom; eassumption.
      + eapply RomStable.sys_rob_wrom; eassumption.
      + apply grant_ok_cwrom; exact Hg.
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

  Lemma grant_ok_app_tail : forall c, grant_ok segs c -> grant_ok (segs ++ tail) c.
  Proof.
    intros c H x8 Hx.
    assert (E : sys_input (segs ++ tail) (cfg_ms c) x8 = sys_input segs (cfg_ms c) x8)
      by (eapply RomStable.sys_input_app_nw; eassumption).
    rewrite E. exact (H x8 Hx).
  Qed.

  Theorem rzb_app_tail : forall c T, rzb segs c T -> rzb (segs ++ tail) c T.
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hg Hc IH | c Hh | c T T' H IH Heq].
    - apply (rzb_node (segs ++ tail) c I evs nx T i0).
      + eapply RomStable.node_ok_app_tail; eassumption.
      + eapply RomStable.sys_rob_app_tail; eassumption.
      + apply grant_ok_app_tail; exact Hg.
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

(** The walk bridge over [rzb]: a walk over the binary's own segments, from the binary's
    start, is a walk of the run's start over the run's segment list. *)
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
