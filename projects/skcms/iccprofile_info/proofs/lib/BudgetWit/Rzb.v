(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Info/ShapeAlg.v: the relation realizes with a no-allocation check at each node (rzb), its soundness for the budget premise, and the node lemmas restated over rzb. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, rzb_node takes the read-only-backing premise (RomBase.sys_rob), munmap counts as an allocation call (alloc_mark_sysnos), budget_refused_at's two instruction clauses are premises, and the walk lifts to a larger backing and to the run's segments and start (rzb_wrom, rzb_app_tail, rzb_run_segments, rzb_run_init). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec RelSpec SimInv ExitSim CatSim MmapSim AllocSim.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import ShapeAlg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RomBase RomStable.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

(** * [rzb]: [Info.ShapeAlg.realizes] with a no-allocation check at each node

    [ShapeAlg.realizes segs c T] ties a trace set to the one-step families of
    the configurations a run reaches, for the filtered step
    [sstep_cfg segs ShapeAlg.CFG].  It has no cut, but a derivation records
    nothing about the configurations it passes, so no [realizes] proof says
    that a run is never refused by the budget.  [rzb] has the same three
    constructors, and its node constructor asks, besides [node_ok] and
    [RomBase.sys_rob] (as [ShapeAlg.rz_node] does), for
    [ShapeAlg.nonalloc segs c]: if a syscall is pending at [c], its family is
    not one [ShapeAlg.CFG] reads as forced-only.  [ShapeAlg.CFG] reads only the
    allocation family as forced-only, so the syscall is none of the five
    [FamAlloc] arms (brk 214, munmap 215, mremap 216, mmap 222, mprotect 226,
    [Run.alloc_mark_sysnos]).

    That one fact gives both halves of the budget premise at a node:
    - every step of the unfiltered relation [sstep] from [c] is a step of
      [sstep_cfg segs CFG] ([ShapeAlg.sstep_cfg_of_nonalloc]), so the
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
    restated over [rzb] with their proofs: [rz_] is written [rzb_].  A lemma
    that takes a [node_ok] also takes [nonalloc] for the same configuration; a
    lemma whose node is an instruction or an exit derives it. *)

Section WithSegs.
Variable segs : list Segment.

(** Off the forced-only allocation family, the budget refuses no grant. *)
Lemma nonalloc_grant : forall c x8,
  nonalloc segs c -> ms_svc_pending (cfg_ms c) = Some x8 ->
  alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = false.
Proof.
  intros c x8 Hna Hx. apply alloc_budget_refused_b_outside.
  pose proof (Hna x8 Hx) as Hoff. unfold injected_family_off in Hoff. cbv beta in Hoff.
  revert Hoff. generalize (bv_unsigned (in_sysno (sys_input segs (cfg_ms c) x8))) as n.
  intros n Hoff Hin. cbn [alloc_mark_sysnos In] in Hin.
  (* LPS 727298f3: [Run.alloc_mark_sysnos] also lists munmap (215), an allocation-family
     arm too, so [CFG] reads it as forced-only as well. *)
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]]; vm_compute in Hoff; discriminate Hoff.
Qed.

Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (* LPS 08b1429: the node's syscall reads the same over a larger read-only backing, so a
       walk over the binary's own segments lifts to the run's segment list
       ([rzb_run_init]).  [ShapeAlg.rz_node] asks the same, in the same place. *)
    RomBase.sys_rob segs c ->
    nonalloc segs c ->
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
  node_ok segs c I evs nx -> nonalloc segs c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ Hc] Hna [Hh Hr].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs.
    destruct (Hc [] SError (sstep_cfg_of_nonalloc segs _ [] SError Hna Hs)) as (i & _ & Hbad).
    discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hr.
  (* LPS 727298f3: [Run.budget_refused_at]'s instruction half is TWO clauses --
     the first-touch fault and the vDSO materialization fault -- and both are premises
     of an [SError] step ([Run.budget_fault_instr_sstep_error],
     [Run.budget_fault_vdso_sstep_error]), so both close the same way. *)
  destruct Hr as [(Hsvc & [ (report & Hstep & Hmat)
                          | (Hacct & fn & n & eff0 & model0 & evs0 & Hfn & Hsys & Hspec0 & Hret0 & Hh0 & Hmat0) ])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr (budget_fault_vdso_sstep_error segs ms model fn n eff0 model0 evs0
                   Hh Hsvc Hacct Hfn Hsys Hspec0 Hret0 Hh0 Hmat0)).
  - pose proof (nonalloc_grant (mkCfg ms model) x8 Hna Hx8) as Hg.
    cbn [cfg_ms cfg_model] in Hg. congruence.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma rzb_star_not_refused : forall c T, rzb c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hrob Hna Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hna).
    + destruct (proj2 Hnode e (SNext c2) (sstep_cfg_of_nonalloc segs c e (SNext c2) Hna Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + intros [Hn _]. exact (Hh Hn).
    + exfalso. exact (Hh (sstep_halted_none segs c e _ Hss)).
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
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hna Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma rzb_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  nonalloc segs c ->
  rzb c' T ->
  rzb c T.
Proof.
  intros c c' T Hnode Hrob Hna Hc.
  apply (rzb_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzb_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob Hna).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply rzb_nonempty; exact Hc ].
Qed.

Lemma rzb_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  nonalloc segs c ->
  rzb c' T ->
  rzb c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hna Hc.
  apply (rzb_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rzb_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob Hna).
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
  eapply rzb_silent1;
    [ apply node_instr; eassumption
    | apply RomBase.sys_rob_instr; cbn [cfg_ms]; exact Hsvc
    | apply nonalloc_instr; exact Hsvc | exact Hc].
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
  assert (Hna : nonalloc segs (mkCfg ms model)).
  { apply (nonalloc_no segs ms model x8 Hsvc). unfold alloc_no.
    destruct Hx8 as [E | E]; rewrite E; reflexivity. }
  unfold t_exit.
  eapply (rzb_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - apply (node_ok_of_s segs); [exact Hna |].
    split.
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
  - exact Hna.
  - apply rzb_halt. cbn. discriminate.
Qed.

End WithSegs.

(** ** The walk over the binary's own segments, lifted to the run

    LPS 08b1429: [Run.run_scfg_budget_refused] reads the run against
    [run_segments segs inp sp mbase] -- the binary's segments with the run's vDSO
    appended -- and from the start configuration over that list.  A walk is built
    over the binary's own segments, so it has to be lifted, exactly as
    [Info.RomStable.run_init] lifts a [ShapeAlg.realizes] walk.  These are that
    file's three theorems over [rzb]; every node-level step is RomStable's own, and
    the only new part is that [nonalloc] is untouched by a change of the read-only
    backing or of the segment list. *)

(** [nonalloc] reads only the pending syscall's number, which [Run.sys_input] copies
    whatever the read-only backing and the segment list are. *)
Lemma nonalloc_cwrom : forall segs c r, nonalloc segs c -> nonalloc segs (RomBase.cwrom c r).
Proof. intros segs [ms model] r H x8 Hx. exact (H x8 Hx). Qed.

Lemma nonalloc_app_tail : forall segs tail c, nonalloc segs c -> nonalloc (segs ++ tail) c.
Proof. intros segs tail [ms model] H x8 Hx. exact (H x8 Hx). Qed.

Section RzbWrom.
  Variable segs : list Segment.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_wrom : forall c T, rzb segs c T ->
    forall r, RomBase.rom_ext (ms_rom (cfg_ms c)) r -> rzb segs (RomBase.cwrom c r) T.
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hna Hc IH | c Hh | c T T' H IH Heq];
    intros r Hr.
    - apply (rzb_node segs (RomBase.cwrom c r) I evs (fun i => RomBase.cwrom (nx i) r) T i0).
      + eapply RomStable.node_wrom; eassumption.
      + eapply RomStable.sys_rob_wrom; eassumption.
      + exact (nonalloc_cwrom segs c r Hna).
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
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hna Hc IH | c Hh | c T T' H IH Heq].
    - apply (rzb_node (segs ++ tail) c I evs nx T i0).
      + eapply RomStable.node_ok_app_tail; eassumption.
      + eapply RomStable.sys_rob_app_tail; eassumption.
      + exact (nonalloc_app_tail segs tail c Hna).
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

(** The supplier-walk bridge over [rzb]: a walk over the binary's own segments, from the
    binary's start, is a walk of the run's start over the run's segment list. *)
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
