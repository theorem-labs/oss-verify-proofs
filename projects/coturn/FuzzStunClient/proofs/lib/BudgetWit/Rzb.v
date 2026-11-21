(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Common/ShapeAlg.v: the relation realizes with a budget check at each node (rzb), its soundness for the budget premise, and ShapeAlg's node lemmas restated over rzb. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, rzb_node takes the read-only-backing premise (RomBase.sys_rob), budget_refused_at's two instruction clauses, the first-touch fault and the vDSO materialization fault, are premises of an SError step, which node_not_refused uses for both, and the walk lifts to the run's segments and start (rzb_run_segments, rzb_run_init) and across the vDSO draw (rzb_with_vdso_no_text); lines 132-141 of projects/bzip2/bzip2_compress_target/proofs/lib/BudgetWit/Rzb.v as in the LPS 727298f3 update are taken, with their comment worded for this tree, and the lift takes the shape of its lines 299-369. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SimInv ExitSim CatSim MmapSim AllocSim AllocSim2 WallSim ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.Cfg Require RomBase RomStable.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require RunSegTail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(** * [rzb]: [ShapeAlg.realizes] with a budget check at each node

    [ShapeAlg.realizes segs c T] ties a trace set to the one-step
    families of the configurations a run reaches.  In this tree [node_ok] reads
    the unfiltered step [sstep segs], and [realizes] has three constructors,
    [rz_node], [rz_halt] and [rz_conseq]: there is no cut.  The completeness
    half of [node_ok] already excludes an [SError] step, so the two first-touch
    clauses of [Run.budget_refused_at] cannot hold at a node
    ([Run.budget_fault_instr_sstep_error],
    [Run.budget_fault_syscall_sstep_error]).  The third clause, the budget
    refusing a grant, is not a step: a [realizes] derivation records nothing
    about it, so no [realizes] proof says that a run is never refused by the
    budget.

    [rzb] has the same three constructors, and its node constructor asks,
    besides [node_ok], for [budget_ok segs c]: if a syscall is pending at [c],
    the budget mark [Run.alloc_budget_refused_b] answers [false] on it.  That
    holds at an instruction ([budget_ok_instr]) and at a syscall whose number is
    none of 214, 216, 222 and 226, the RISC-V Linux numbers of brk, mremap, mmap
    and mprotect ([Run.alloc_mark_sysnos]; [budget_ok_nonalloc],
    [budget_ok_num], [budget_ok_exit]).

    [rzb_never_refused]: no configuration the unfiltered run reaches from an
    [rzb] configuration is budget-refused; [rzb_never_refused_cfg]: nor under any
    spurious-failure configuration ([Run.reaches_budget_refused_cfg_sub]).

    LPS 08b1429 and later: [Run.run_budget_refused] and [Run.run_scfg_budget_refused]
    read the run over [run_segments segs inp sp mbase] (the binary's segments with the
    run's vDSO pair appended) from the start configuration over that list, so the node
    constructor also asks [RomBase.sys_rob segs c], as [ShapeAlg.rz_node] does, and
    [rzb_run_init] at the end of this file lifts a walk over the binary's own segments
    to the run's.

    The rest of the file is ShapeAlg's lemmas that build a
    [realizes] node, restated over [rzb] with ShapeAlg's proofs:
    [rz_] is written [rzb_].  A lemma that takes a [node_ok] also takes
    [RomBase.sys_rob] and [budget_ok] for the same configuration; a lemma whose
    node is an instruction or an exit derives them. *)

Section g.
Variable segs : list Segment.

(** If a syscall is pending at [c], the budget does not refuse it as a grant. *)
Definition budget_ok (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = false.

Lemma budget_ok_instr : forall ms model,
  ms_svc_pending ms = None -> budget_ok (mkCfg ms model).
Proof.
  intros ms model Hsvc x8 Hx. cbn [cfg_ms] in Hx. rewrite Hsvc in Hx. discriminate Hx.
Qed.

Lemma budget_ok_nonalloc : forall ms model x8,
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  budget_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hn y Hy. cbn [cfg_ms cfg_model] in *. rewrite Hsvc in Hy.
  injection Hy as <-. apply alloc_budget_refused_b_outside. rewrite in_sysno_sys_input. exact Hn.
Qed.

(** The form a walk gives: the number as a literal, checked by [existsb]. *)
Lemma budget_ok_num : forall ms model x8 n,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n ->
  existsb (Z.eqb n) alloc_mark_sysnos = false ->
  budget_ok (mkCfg ms model).
Proof.
  intros ms model x8 n Hsvc Hx Hb. apply (budget_ok_nonalloc ms model x8 Hsvc).
  rewrite Hx. intros Hin.
  assert (Ht : existsb (Z.eqb n) alloc_mark_sysnos = true).
  { apply existsb_exists. exists n. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

(** The exit (93 or 94) is off the four allocation numbers. *)
Lemma budget_ok_exit : forall ms model x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 -> budget_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc [Hx | Hx];
    exact (budget_ok_num ms model x8 _ Hsvc Hx eq_refl).
Qed.
End g.

Section d.
Variable segs : list Segment.

Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (* LPS 08b1429: the node's syscall reads the same over a larger read-only backing, so a
       walk over the binary's own segments lifts to the run's segment list
       ([rzb_run_init]).  [ShapeAlg.rz_node] asks the same, in the same place. *)
    RomBase.sys_rob segs c ->
    budget_ok segs c ->
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

(** A node with the budget check is not budget-refused. *)
Lemma node_not_refused : forall c I evs nx,
  node_ok segs c I evs nx -> budget_ok segs c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ Hc] Hb [Hh Hr].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs. destruct (Hc [] SError Hs) as (i & _ & Hbad). discriminate Hbad. }
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
  - pose proof (Hb x8 Hx8) as Hg. cbn [cfg_ms cfg_model] in Hg. congruence.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma rzb_star_not_refused : forall c T, rzb segs c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hb).
    + destruct (proj2 Hnode e (SNext c2) Hss) as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + intros [Hn _]. exact (Hh Hn).
    + exfalso. exact (Hh (sstep_halted_none segs c e _ Hss)).
  - exact (IH tr c' Hstar).
Qed.

(** No configuration the unfiltered run reaches from an [rzb] configuration is
    budget-refused. *)
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
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma rzb_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  budget_ok segs c ->
  rzb segs c' T ->
  rzb segs c T.
Proof.
  intros c c' T Hnode Hrob Hb Hc.
  apply (rzb_conseq segs c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzb_node segs c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob Hb).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply rzb_nonempty; exact Hc ].
Qed.

Lemma rzb_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  budget_ok segs c ->
  rzb segs c' T ->
  rzb segs c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hb Hc.
  apply (rzb_conseq segs c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rzb_node segs c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob Hb).
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
    | apply budget_ok_instr; exact Hsvc | exact Hc].
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
  - (* 93/94 do not read [in_mem]: [RomBase.memfree_93]/[memfree_94] through [sys_rob_exit] *)
    exact (RomBase.sys_rob_exit segs ms model x8 Hsvc Hx8).
  - exact (budget_ok_exit segs ms model x8 Hsvc Hx8).
  - apply rzb_halt. cbn. discriminate.
Qed.

End WithSegs.

(** ** The walk over the binary's own segments, lifted to the run

    LPS 08b1429: [Run.run_budget_refused] and [Run.run_scfg_budget_refused] read the run
    against [run_segments segs inp sp mbase] -- the binary's segments with the run's vDSO
    pair appended -- and from the start configuration over that list.  A walk is built over
    the binary's own segments, so it has to be lifted, exactly as [RomStable.realizes_run_init]
    and [RunSegTail.realizes_run_segments] lift a [ShapeAlg.realizes] walk.  These are those
    theorems over [rzb]; every node-level step is theirs, and the only new part is that
    [budget_ok] -- which reads the pending number and the argument registers alone
    ([Run.alloc_budget_refused_b]) -- is untouched by a change of the read-only backing or
    of the segment list.  The shape is that of lines 299-369 of
    projects/bzip2/bzip2_compress_target/proofs/lib/BudgetWit/Rzb.v as in the LPS 727298f3 update,
    with its [nalloc_ok] read as this file's [budget_ok]. *)

Lemma alloc_budget_refused_b_sys_args : forall i i' m,
  in_sysno i = in_sysno i' -> in_args i = in_args i' ->
  alloc_budget_refused_b i m = alloc_budget_refused_b i' m.
Proof. intros i i' m Hs Ha. unfold alloc_budget_refused_b, in_arg. rewrite Hs, Ha. reflexivity. Qed.

Lemma budget_ok_cwrom : forall segs c r, budget_ok segs c -> budget_ok segs (RomBase.cwrom c r).
Proof.
  intros segs [ms model] r H x8 Hx.
  transitivity (alloc_budget_refused_b (sys_input segs ms x8) model); [|exact (H x8 Hx)].
  apply alloc_budget_refused_b_sys_args; reflexivity.
Qed.

Lemma budget_ok_app_tail : forall segs tail c, budget_ok segs c -> budget_ok (segs ++ tail) c.
Proof.
  intros segs tail c H x8 Hx.
  transitivity (alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c)); [|exact (H x8 Hx)].
  apply alloc_budget_refused_b_sys_args; reflexivity.
Qed.

Section RzbWrom.
  Variable segs : list Segment.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_wrom : forall c T, rzb segs c T ->
    forall r, RomBase.rom_ext (ms_rom (cfg_ms c)) r -> rzb segs (RomBase.cwrom c r) T.
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq];
    intros r Hr.
    - apply (rzb_node segs (RomBase.cwrom c r) I evs (fun i => RomBase.cwrom (nx i) r) T i0).
      + eapply RomStable.node_wrom; eassumption.
      + eapply RomStable.sys_rob_wrom; eassumption.
      + apply budget_ok_cwrom; exact Hb.
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
    induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq].
    - apply (rzb_node (segs ++ tail) c I evs nx T i0).
      + eapply RunSegTail.node_ok_app_tail; eassumption.
      + eapply RunSegTail.sys_rob_app_tail; eassumption.
      + apply budget_ok_app_tail; exact Hb.
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
           (fun s Hs => RunSegTail.vdso_segments_nx _ _ _ s Hs)
           (fun s Hs => RunSegTail.vdso_segments_nw _ _ _ s Hs) Hvi).
  exact H.
Qed.

(** A walk over the binary's own segments, from the binary's start, is a walk of the run's
    start over the run's segment list. *)
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
  cbn [cfg_ms init_config]. apply RomStable.seg_rom_run_segments_ext.
Qed.

(** ** Bridge (A) over [rzb]: the launch's vDSO draw

    [Common/VdsoBridge.v]'s [realizes_with_vdso] and [realizes_with_vdso_no_text], statement
    and proof, over [rzb]: the start-up walk hands over a model that carries the launch's vDSO
    draw ([with_vdso], as [Run.init_config] does), and the usage walk is stated without it.  The
    only new obligation is the budget check at the wrapped node, and [Run.alloc_budget_refused_b]
    ignores the draw ([VdsoCommuteCfg.alloc_budget_refused_b_with_vdso]). *)
From LinuxProcessSemantics.LinuxProcessSem Require Import VdsoCommute VdsoCommuteSys.
From LinuxProcessSemantics.LinuxProcessSem Require VdsoCommuteCfg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require VdsoBridge.

Lemma budget_ok_cfg_with_vdso : forall segs v c, budget_ok segs c -> budget_ok segs (cfg_with_vdso v c).
Proof.
  intros segs v [ms m] H x8 Hx.
  change (alloc_budget_refused_b (sys_input segs ms x8) (with_vdso v m) = false).
  rewrite VdsoCommuteCfg.alloc_budget_refused_b_with_vdso. exact (H x8 Hx).
Qed.

Section RzbVdso.
Variable segs : list Segment.

Theorem rzb_with_vdso : forall (P : config -> Prop),
  (forall c, P c -> vdso_entry_fn segs (ms_pc (cfg_ms c)) = None) ->
  (forall c evs c', P c -> sstep segs c evs (SNext c') -> P c') ->
  forall c T, rzb segs c T -> P c -> forall v, rzb segs (cfg_with_vdso v c) T.
Proof.
  intros P Hpc Hstep c T H.
  induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq]; intros HP v.
  - destruct Hnode as [Hs Hc].
    pose proof (Hpc c HP) as Hnv.
    (* the forward image of each original transition *)
    assert (W : forall i, sstep segs (cfg_with_vdso v c) (evs i) (SNext (cfg_with_vdso v (nx i)))).
    { intros i. exact (sstep_cfg_with_vdso segs v c (evs i) (SNext (nx i)) Hnv (Hs i)). }
    set (I' := {i : I & {c'' : config | (exists w, c'' = cfg_with_vdso w (nx i))
                                        /\ sstep segs (cfg_with_vdso v c) (evs i) (SNext c'')}}).
    set (pick := fun i : I => @existT I (fun i => {c'' : config | (exists w, c'' = cfg_with_vdso w (nx i))
                                        /\ sstep segs (cfg_with_vdso v c) (evs i) (SNext c'')})
                                     i (exist _ (cfg_with_vdso v (nx i)) (conj (ex_intro _ v eq_refl) (W i)))).
    apply (rzb_conseq segs _ (t_alt (fun i' : I' => t_emit (evs (projT1 i')) (T (projT1 i'))))).
    + apply (rzb_node segs _ I' (fun i' => evs (projT1 i')) (fun i' => proj1_sig (projT2 i'))
               (fun i' => T (projT1 i')) (pick i0)).
      * split.
        -- intros [i [c'' Hp]]. exact (proj2 Hp).
        -- intros e st Hst.
           assert (Hnv' : vdso_entry_fn segs (ms_pc (cfg_ms (cfg_with_vdso v c))) = None) by exact Hnv.
           pose proof (sstep_cfg_with_vdso segs (m_vdso (cfg_model c)) (cfg_with_vdso v c) e st Hnv' Hst) as Hinv.
           rewrite VdsoBridge.cfg_with_vdso_back in Hinv.
           destruct (Hc e _ Hinv) as (i & -> & Hst').
           destruct st as [c''|]; cbn [step_to_with_vdso] in Hst'; [|discriminate].
           injection Hst' as Hc''.
           assert (Hw : c'' = cfg_with_vdso (m_vdso (cfg_model c'')) (nx i)).
           { rewrite <- Hc'', VdsoBridge.cfg_with_vdso_absorb, VdsoBridge.cfg_with_vdso_self. reflexivity. }
           exists (@existT I _ i (exist _ c'' (conj (ex_intro _ _ Hw) Hst))). split; reflexivity.
      * exact (RomBase.sys_rob_cfg_with_vdso segs v c Hrob).
      * exact (budget_ok_cfg_with_vdso segs v c Hb).
      * intros [i [c'' Hp]]. cbn [projT1 projT2 proj1_sig]. destruct (proj1 Hp) as [w Hw]. rewrite Hw.
        exact (IH i (Hstep c (evs i) (nx i) HP (Hs i)) w).
    + intros tr. split.
      * intros [[i s] Hi]. exists i. exact Hi.
      * intros [i Hi]. exists (pick i). exact Hi.
  - apply rzb_halt. unfold cfg_with_vdso. cbn [cfg_model]. rewrite VdsoBridge.m_halted_with_vdso. exact Hh.
  - eapply rzb_conseq; [exact (IH HP v) | exact Heq].
Qed.

(** As [VdsoBridge.realizes_with_vdso_no_text]: over the image's own segments there is no vDSO
    text, so no pc invariant is needed. *)
Corollary rzb_with_vdso_no_text :
  vdso_text_seg segs = None ->
  forall c T, rzb segs c T -> forall v, rzb segs (cfg_with_vdso v c) T.
Proof.
  intros Hnt c T H v.
  apply (rzb_with_vdso (fun _ => True)); [ | | exact H | exact I].
  - intros c' _. exact (vdso_entry_fn_none_of_no_text segs _ Hnt).
  - intros; exact I.
Qed.

End RzbVdso.
