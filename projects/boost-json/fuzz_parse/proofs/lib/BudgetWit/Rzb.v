(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from ShapeAlg.v's realizes and the node lemmas of ShapeAlg.v and Nodes.v that the usage path uses, with a no-allocation-call check at each node; adds the theorem that turns the carrier into the budget premise. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the vDSO arms of the step and of the budget refusal, the system-call robustness premise (sys_rob) in the node's check, and the lift of a walk to the run's segment list (run_segments), a larger read-only backing and the run's vDSO layer. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg RelSpec SimInv ExitSim CatSim MmapSim AllocSim AllocSim2 WallSim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import ShapeAlg Nodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.Cfg Require RomBase RomStable.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** * [realizes]: [ShapeAlg.realizes] with a no-allocation check at each node

    [ShapeAlg.realizes segs c T] ties a trace set to the one-step families of
    the configurations a run reaches, for the filtered step
    [sstep_cfg segs the_scfg].  A derivation records nothing about the
    configurations it passes, so no [ShapeAlg.realizes] proof says that a run is
    never refused by the budget.  [realizes] below has the same three
    constructors in the same order, and its node constructor asks, besides
    [node_ok], for [nonalloc c]: if a system call is pending at [c], its number
    is none of [Run.alloc_mark_sysnos] (brk 214, mremap 216, mmap 222,
    mprotect 226) and [the_scfg] does not read its family as forced-only.

    That one fact gives both halves of the budget premise at a node:
    - every step of the unfiltered relation [sstep] from [c] is a step of
      [sstep_cfg segs the_scfg] ([sstep_cfg_of_nonalloc]), so the completeness
      half of [node_ok] covers it, and the two first-touch clauses of
      [Run.budget_refused_at], each the premise of an [SError] step
      ([Run.budget_fault_instr_sstep_error],
      [Run.budget_fault_syscall_sstep_error]), cannot hold;
    - the grant clause [Run.alloc_budget_refused_b] answers [false] off the four
      allocation numbers ([Run.alloc_budget_refused_b_outside]).

    [realizes_never_refused_cfg]: no configuration the run reaches from a
    [realizes] configuration, under any spurious-failure configuration, is
    budget-refused.

    The names are the released ones ([realizes], [rz_node], [rz_halt],
    [rz_conseq], [rz_msteps], ...), so that a released proof script whose name
    table is pointed at this module is the same proof over this carrier.  The
    rest of the file is the node lemmas the usage path uses, restated over this
    [realizes] with their released proofs.  A lemma that takes a [node_ok] also
    takes [nonalloc] for the same configuration ([rz_silent1], [rz_emit1],
    [rz_cases], [rz_ret_only_copyins_silent]); a lemma whose node is an
    instruction or an exit derives it and keeps the released statement. *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : list Segment.
Context {SC : StepCfg}.

(** The pending system call, if any, is off the allocation numbers and off the
    families [the_scfg] reads as forced-only; and it reads the same over every larger
    read-only backing ([RomBase.sys_rob], which [ShapeAlg.rz_node] asks in the same place),
    so that a walk over the binary's own segments lifts to the run ([realizes_wrom]). *)
Definition nonalloc (c : config) : Prop :=
  (forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    ~ In (bv_unsigned x8) alloc_mark_sysnos /\
    injected_family_off the_scfg (sys_input segs (cfg_ms c) x8) = false)
  /\ RomBase.sys_rob segs c.

Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    nonalloc c ->
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes c t_nil
| rz_conseq : forall c T T',
    realizes c T -> t_eq T T' -> realizes c T'.

(** An instruction configuration has no pending system call. *)
Lemma nonalloc_instr : forall ms model, ms_svc_pending ms = None -> nonalloc (mkCfg ms model).
Proof.
  intros ms model H. split.
  - intros x8 H'. cbn [cfg_ms] in H'. congruence.
  - apply RomBase.sys_rob_instr. cbn [cfg_ms]. exact H.
Qed.

(** A pending system call with no injecting arm, off the allocation numbers, whose
    specification reads the same over every larger read-only backing. *)
Lemma nonalloc_no : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  injected_arm (bv_unsigned x8) = None ->
  existsb (Z.eqb (bv_unsigned x8)) alloc_mark_sysnos = false ->
  RomBase.sys_rob segs (mkCfg ms model) ->
  nonalloc (mkCfg ms model).
Proof.
  intros ms model x8 Hs Ha Hb Hrob. split; [|exact Hrob].
  intros y Hy. cbn [cfg_ms] in Hy |- *.
  rewrite Hs in Hy. injection Hy as <-. split.
  - intros Hin. apply Bool.not_true_iff_false in Hb. apply Hb.
    apply existsb_exists. exists (bv_unsigned x8). split; [exact Hin | apply Z.eqb_refl].
  - unfold injected_family_off. rewrite in_sysno_sys_input, Ha. reflexivity.
Qed.

(** Off a forced-only family, every unfiltered step is a filtered one. *)
Lemma sstep_cfg_of_nonalloc : forall c e st,
  nonalloc c -> sstep segs c e st -> sstep_cfg segs the_scfg c e st.
Proof.
  intros c e st Hna H. destruct H as
    [ms model ms' model' Hh Hsvc Hacc
    | ms model Hh Hsvc Hacc
    | ms model Hh Hsvc Hacc Hvd
    | ms model fn n eff model' model'' evs Hh Hsvc Hacc Hvd Hfn Hspec Hre Hh' Hmat
    | ms model fn n eff model' evs Hh Hsvc Hacc Hvd Hfn Hspec Hre Hh' Hmat
    | ms model fn Hh Hsvc Hacc Hvd Hun
    | ms model x8 eff model' model'' evs Hh Hsvc Hspec Hh' Hmat
    | ms model x8 eff model' evs Hh Hsvc Hspec Hh' Hmat
    | ms model x8 eff model' evs code Hh Hsvc Hspec Hh' Hk
    | ms model x8 eff model' evs sig Hh Hsvc Hspec Hk
    | ms model x8 Hh Hsvc Hspec].
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
  (* LPS 727298f3: the three vDSO arms, which [sstep_cfg] mirrors with no filter premise *)
  - eapply sstep_cfg_vdso_call; eassumption.
  - eapply sstep_cfg_vdso_materialization_fault; eassumption.
  - eapply sstep_cfg_vdso_unmodeled; eassumption.
  - eapply sstep_cfg_syscall; try eassumption.
    intros (Hoff & _ & _). destruct (proj1 Hna x8 Hsvc) as [_ Hna'].
    cbn [cfg_ms] in Hna'. rewrite Hna' in Hoff. discriminate.
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    intros (Hoff & _ & _). destruct (proj1 Hna x8 Hsvc) as [_ Hna'].
    cbn [cfg_ms] in Hna'. rewrite Hna' in Hoff. discriminate.
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Lemma sstep_halted_none_b : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

(** ** Soundness for the budget premise *)

(** A node with the check is not budget-refused. *)
Lemma node_not_refused : forall c I evs nx,
  node_ok segs c I evs nx -> nonalloc c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ Hc] Hna [Hh Hr].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs.
    destruct (Hc [] SError (sstep_cfg_of_nonalloc _ [] SError Hna Hs)) as (i & _ & Hbad).
    discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hr.
  (* LPS 727298f3: the no-syscall branch of [Run.budget_refused_at] also holds a
     faulting vDSO call ([Run.budget_fault_vdso_sstep_error]). *)
  destruct Hr as [(Hsvc & [(report & Hstep & Hmat)
                          | (Hun & fn & n & eff & model' & evs' & Hfn & Hn & Hspec & Hef & Hh' & Hmat)])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr (budget_fault_vdso_sstep_error segs ms model fn n eff model' evs' Hh Hsvc Hun Hfn Hn Hspec Hef Hh' Hmat)).
  - destruct (proj1 Hna x8 Hx8) as [Hno _].
    rewrite alloc_budget_refused_b_outside in Hgr; [discriminate Hgr|].
    rewrite in_sysno_sys_input. exact Hno.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma star_cases : forall c tr c', star segs c tr c' ->
  c' = c \/ exists e c2 tr2, sstep segs c e (SNext c2) /\ star segs c2 tr2 c'.
Proof.
  intros c tr c' H. destruct H as [c0 | c1 e c2 tr2 c3 Hss Hstar].
  - left. reflexivity.
  - right. exists e, c2, tr2. split; [exact Hss | exact Hstar].
Qed.

Lemma realizes_star_not_refused : forall c T, realizes c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hna Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hna).
    + destruct (proj2 Hnode e (SNext c2) (sstep_cfg_of_nonalloc c e (SNext c2) Hna Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + intros [Hn _]. exact (Hh Hn).
    + exfalso. exact (Hh (sstep_halted_none_b c e _ Hss)).
  - exact (IH tr c' Hstar).
Qed.

(** No configuration the run reaches from a [realizes] configuration is
    budget-refused... *)
Theorem realizes_never_refused : forall c T, realizes c T -> ~ reaches_budget_refused segs c.
Proof.
  intros c T H (tr & c' & Hstar & Hb). exact (realizes_star_not_refused c T H tr c' Hstar Hb).
Qed.

(** ...and so none the run under any spurious-failure configuration reaches
    ([Run.reaches_budget_refused_cfg_sub]). *)
Theorem realizes_never_refused_cfg : forall cfg c T, realizes c T ->
  ~ reaches_budget_refused_cfg segs cfg c.
Proof.
  intros cfg c T H Hr. exact (realizes_never_refused c T H (reaches_budget_refused_cfg_sub segs cfg c Hr)).
Qed.

(** ** ShapeAlg's node lemmas over [realizes] *)

Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hna Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma rz_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  nonalloc c ->
  realizes c' T ->
  realizes c T.
Proof.
  intros c c' T Hnode Hna Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hna).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

Lemma rz_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  nonalloc c ->
  realizes c' T ->
  realizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hna Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hna).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(** An instruction step: the released statement, no new premise. *)
Lemma rz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rz_silent1;
    [ apply node_instr; eassumption
    | apply nonalloc_instr; exact Hsvc
    | exact Hc ].
Qed.

Lemma rz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                  | apply IH; exact Hc].
Qed.

(** An exit node: the released statement; [is_exit_no] gives [nonalloc]. *)
Lemma rz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes (mkCfg ms model)
      (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  assert (Hna : nonalloc (mkCfg ms model)).
  { apply (nonalloc_no ms model x8 Hsvc);
      [ destruct Hx8 as [E | E]; rewrite E; reflexivity
      | destruct Hx8 as [E | E]; rewrite E; reflexivity
      | exact (RomBase.sys_rob_exit segs ms model x8 Hsvc Hx8) ]. }
  unfold t_exit.
  eapply (rz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - split.
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_cfg_exit segs the_scfg ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss. apply sstep_cfg_sub in Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
  - exact Hna.
  - apply rz_halt. cbn. discriminate.
Qed.

(** ** Nodes.v's node lemmas over [realizes] *)

Lemma rz_ret_only_copyins_silent : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <->
             o = Ok (with_copyins reads (mkEffectU r [] [] [] [] [])) m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  nonalloc (mkCfg ms model) ->
  realizes (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hlazy Hna Hc.
  eapply rz_silent1; [eapply node_ret_only_copyins; eassumption | exact Hna | exact Hc].
Qed.

Lemma rz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  nonalloc c ->
  (forall i, realizes (nx i) (T i)) ->
  realizes c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hna Hc.
  apply (rz_conseq c (t_alt (fun i => t_emit [] (T i)))).
  - apply (rz_node c I (fun _ => []) nx T i0 Hnode Hna Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (realizes_nonempty _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (realizes_nonempty _ _ (Hc i)) tr) Hi).
Qed.

End WithSegs.

(** ** The walk over the binary's own segments, lifted to the run

    LPS 727298f3: [Run.run_scfg_budget_refused] reads the run over
    [run_segments segs inp sp mbase] (the binary's segments with the run's vDSO pair
    appended), from a start whose model carries the run's vDSO layer, while the main
    phase is walked over the binary's own segments with no vDSO layer.  The walk is lifted
    as RefTop.v lifts a [ShapeAlg.realizes] walk ([RomStable.realizes_wrom],
    [RomStable.realizes_run_segments], [VdsoBridge.realizes_with_vdso_no_text]): every
    node-level step is theirs, and [nonalloc] survives each change, since it reads
    [ms_svc_pending], the system-call number and [RomBase.sys_rob]. *)

From LinuxProcessSemantics.LinuxProcessSem Require Import VdsoCommute VdsoCommuteSys VdsoCommuteCfg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common Require VdsoBridge.

Section Lift.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {SC : StepCfg}.

  (* a larger read-only backing *)
  Section Wrom.
    Variable segs : list Segment.
    Hypothesis Hvi : vdso_image segs = None.

    Lemma nonalloc_cwrom : forall c r, nonalloc segs c ->
      RomBase.rom_ext (ms_rom (cfg_ms c)) r -> nonalloc segs (RomBase.cwrom c r).
    Proof.
      intros c r [Hna Hrob] Hr. split.
      - intros x8 Hs.
        change (ms_svc_pending (cfg_ms (RomBase.cwrom c r))) with (ms_svc_pending (cfg_ms c)) in Hs.
        destruct (Hna x8 Hs) as [H1 H2]. split; [exact H1|].
        change (cfg_ms (RomBase.cwrom c r)) with (RomBase.wrom (cfg_ms c) r).
        rewrite RomBase.sys_input_wrom. exact H2.
      - eapply RomStable.sys_rob_wrom; eassumption.
    Qed.

    Theorem realizes_wrom : forall c T, realizes segs c T ->
      forall r, RomBase.rom_ext (ms_rom (cfg_ms c)) r -> realizes segs (RomBase.cwrom c r) T.
    Proof.
      intros c T H; induction H as [c I evs nx T i0 Hn Hna Hc IH | c Hh | c T T' H IH Heq]; intros r Hr.
      - pose proof (proj2 Hna) as Hrob.
        apply (rz_node segs (RomBase.cwrom c r) I evs (fun i => RomBase.cwrom (nx i) r) T i0).
        + eapply RomStable.node_wrom; eassumption.
        + exact (nonalloc_cwrom c r Hna Hr).
        + intros i. apply IH. erewrite RomStable.node_rom by eassumption. exact Hr.
      - apply rz_halt. exact Hh.
      - eapply rz_conseq; [apply IH; exact Hr | exact Heq].
    Qed.
  End Wrom.

  (* a tail of segments that is neither executable nor writable *)
  Section AppTail.
    Variables segs tail : list Segment.
    Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
    Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
    Hypothesis Hvi : vdso_image segs = None.

    Lemma nonalloc_app_tail : forall c, nonalloc segs c -> nonalloc (segs ++ tail) c.
    Proof.
      intros c [Hna Hrob]. split.
      - intros x8 Hs. erewrite RomStable.sys_input_app_nw by eassumption. exact (Hna x8 Hs).
      - eapply RomStable.sys_rob_app_tail; eassumption.
    Qed.

    Theorem realizes_app_tail : forall c T, realizes segs c T -> realizes (segs ++ tail) c T.
    Proof.
      intros c T H; induction H as [c I evs nx T i0 Hn Hna Hc IH | c Hh | c T T' H IH Heq].
      - apply (rz_node (segs ++ tail) c I evs nx T i0).
        + eapply RomStable.node_ok_app_tail; eassumption.
        + exact (nonalloc_app_tail c Hna).
        + exact IH.
      - apply rz_halt. exact Hh.
      - eapply rz_conseq; [exact IH | exact Heq].
    Qed.
  End AppTail.

  Theorem realizes_run_segments : forall segs inp (sp mb : word) c T,
    vdso_image segs = None ->
    realizes segs c T -> realizes (run_segments segs inp sp mb) c T.
  Proof.
    intros segs inp sp mb c T Hvi H. unfold run_segments.
    apply (realizes_app_tail segs _
             (fun s Hs => RomStable.vdso_segments_nx _ _ _ s Hs)
             (fun s Hs => RomStable.vdso_segments_nw _ _ _ s Hs) Hvi).
    exact H.
  Qed.

  (* the vDSO layer: VdsoBridge.v's [realizes_with_vdso], over this [realizes] *)
  Lemma nonalloc_cfg_with_vdso : forall segs v c, nonalloc segs c -> nonalloc segs (cfg_with_vdso v c).
  Proof.
    intros segs v [ms m] [Hna Hrob]. split.
    - exact Hna.
    - exact (RomBase.sys_rob_cfg_with_vdso segs v (mkCfg ms m) Hrob).
  Qed.

  Theorem realizes_with_vdso : forall segs (P : config -> Prop),
    (forall c, P c -> vdso_entry_fn segs (ms_pc (cfg_ms c)) = None) ->
    (forall c evs c', P c -> sstep_cfg segs the_scfg c evs (SNext c') -> P c') ->
    forall c T, realizes segs c T -> P c -> forall v, realizes segs (cfg_with_vdso v c) T.
  Proof.
    intros segs P Hpc Hstep c T H.
    induction H as [c I evs nx T i0 Hnode Hna Hcont IH | c Hh | c T T' H IH Heq]; intros HP v.
    - destruct Hnode as [Hs Hc].
      pose proof (Hpc c HP) as Hnv.
      assert (W : forall i, sstep_cfg segs the_scfg (cfg_with_vdso v c) (evs i) (SNext (cfg_with_vdso v (nx i)))).
      { intros i. exact (sstep_cfg_vdso_frame_c segs the_scfg v c (evs i) (SNext (nx i)) Hnv (Hs i)). }
      set (I' := {i : I & {c'' : config | (exists w, c'' = cfg_with_vdso w (nx i))
                                          /\ sstep_cfg segs the_scfg (cfg_with_vdso v c) (evs i) (SNext c'')}}).
      set (pick := fun i : I => @existT I (fun i => {c'' : config | (exists w, c'' = cfg_with_vdso w (nx i))
                                          /\ sstep_cfg segs the_scfg (cfg_with_vdso v c) (evs i) (SNext c'')})
                                       i (exist _ (cfg_with_vdso v (nx i)) (conj (ex_intro _ v eq_refl) (W i)))).
      apply (rz_conseq segs _ (t_alt (fun i' : I' => t_emit (evs (projT1 i')) (T (projT1 i'))))).
      + apply (rz_node segs _ I' (fun i' => evs (projT1 i')) (fun i' => proj1_sig (projT2 i'))
                 (fun i' => T (projT1 i')) (pick i0)).
        * split.
          -- intros [i [c'' Hp]]. exact (proj2 Hp).
          -- intros e st Hst.
             assert (Hnv' : vdso_entry_fn segs (ms_pc (cfg_ms (cfg_with_vdso v c))) = None) by exact Hnv.
             pose proof (sstep_cfg_vdso_frame_c segs the_scfg (m_vdso (cfg_model c)) (cfg_with_vdso v c) e st Hnv' Hst)
               as Hinv.
             rewrite VdsoBridge.cfg_with_vdso_back in Hinv.
             destruct (Hc e _ Hinv) as (i & -> & Hst').
             destruct st as [c''|]; cbn [step_to_with_vdso] in Hst'; [|discriminate].
             injection Hst' as Hc''.
             assert (Hw : c'' = cfg_with_vdso (m_vdso (cfg_model c'')) (nx i)).
             { rewrite <- Hc'', VdsoBridge.cfg_with_vdso_absorb, VdsoBridge.cfg_with_vdso_self. reflexivity. }
             exists (@existT I _ i (exist _ c'' (conj (ex_intro _ _ Hw) Hst))). split; reflexivity.
        * exact (nonalloc_cfg_with_vdso segs v c Hna).
        * intros [i [c'' Hp]]. cbn [projT1 projT2 proj1_sig]. destruct (proj1 Hp) as [w Hw]. rewrite Hw.
          exact (IH i (Hstep c (evs i) (nx i) HP (Hs i)) w).
      + intros tr. split.
        * intros [[i s] Hi]. exists i. exact Hi.
        * intros [i Hi]. exists (pick i). exact Hi.
    - apply rz_halt. unfold cfg_with_vdso. cbn [cfg_model]. rewrite VdsoBridge.m_halted_with_vdso. exact Hh.
    - eapply rz_conseq; [exact (IH HP v) | exact Heq].
  Qed.

  (** Over a segment list with no vDSO text every pc is away from an exported entry. *)
  Corollary realizes_with_vdso_no_text : forall segs,
    vdso_text_seg segs = None ->
    forall c T, realizes segs c T -> forall v, realizes segs (cfg_with_vdso v c) T.
  Proof.
    intros segs Hnt c T H v.
    apply (realizes_with_vdso segs (fun _ => True)); [ | | exact H | exact I].
    - intros c' _. exact (vdso_entry_fn_none_of_no_text segs _ Hnt).
    - intros; exact I.
  Qed.
End Lift.
