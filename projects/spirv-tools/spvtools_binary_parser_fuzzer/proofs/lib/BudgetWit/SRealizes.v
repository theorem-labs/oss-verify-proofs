(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from SRealizes.v: the relation srealizes with a no-allocation-call check at each node, its soundness for the budget premise, and SRealizes' node lemmas restated with that check. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the budget refusal of a vDSO call whose effect cannot be materialized, and one more non-allocating syscall in the case split; each node also asks that its system call answers the same over a larger read-only backing (RomBase.sys_rob), so that a walk over the binary's own segments lifts to the run's segments, run_segments, from the run's own start). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim MmapSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.Cfg Require RomBase SRomStable.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(** * [srealizes] with a no-allocation-call check at each node

    The released [SRealizes.srealizes segs c T] ties a trace set to the one-step
    families of the configurations a run reaches.  It has no cut, but a derivation
    records nothing about the configurations it passes, so no [srealizes] proof says
    that a run is never refused by the budget.  This [srealizes] has the same three
    constructors in the same order; [srz_node] also asks [ScfgBase.sys_nonalloc segs c]:
    if a syscall is pending at [c], it is none of the four allocation numbers 214,
    216, 222 and 226 (brk, mremap, mmap, mprotect).  The proofs of the usage path
    replay unchanged over it: they reach the node constructor only through the
    lemmas below and through [SNodes] and [SLibWritev], which supply the check.

    In this tree [node_ok] is stated over [sstep_cfg segs CFG], the run whose
    allocation calls fail only when forced ([ScfgBase.CFG]), not over the unfiltered
    [sstep].  At a configuration with [sys_nonalloc] the two agree: every [sstep]
    from there is an [sstep_cfg segs CFG] step ([ScfgBase.sstep_cfg_of_sstep]).  So
    the completeness half of [node_ok] covers every unfiltered step, and the same
    fact gives the budget mark's answer on a pending call
    ([Run.alloc_budget_refused_b_outside]).

    [srz_never_refused]: no configuration the unfiltered run reaches from an
    [srealizes] configuration is budget-refused.  The two first-touch clauses of
    [Run.budget_refused_at] are premises of an [SError] step
    ([Run.budget_fault_instr_sstep_error], [Run.budget_fault_syscall_sstep_error]),
    which the completeness half of [node_ok] excludes; the grant clause is excluded
    by [sys_nonalloc_budget].  [srz_never_refused_cfg] gives the same for every
    spurious-failure configuration ([Run.reaches_budget_refused_cfg_sub]). *)

(** A number [alloc_sysno_b] rejects is none of the four allocation numbers. *)
Lemma alloc_sysno_b_not_in : forall n, alloc_sysno_b n = false -> ~ In n alloc_mark_sysnos.
Proof.
  intros n H Hin. unfold alloc_mark_sysnos in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; subst n; cbv in H; discriminate H.
Qed.

Section WithSegs.
Variable segs : list Segment.

Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    sys_nonalloc segs c ->
    RomBase.sys_rob segs c ->   (* LPS 08b1429: the node's syscall reads the same over a larger backing *)
    (forall i, srealizes (nx i) (T i)) ->
    srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes c t_nil
| srz_conseq : forall c T T',
    srealizes c T -> t_eq T T' -> srealizes c T'.

Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hna Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

(** ** Soundness *)

(** A pending call that is not an allocation call is not refused as a grant. *)
Lemma sys_nonalloc_budget : forall c x8,
  sys_nonalloc segs c -> ms_svc_pending (cfg_ms c) = Some x8 ->
  alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = false.
Proof.
  intros c x8 Hna Hx. apply alloc_budget_refused_b_outside. apply alloc_sysno_b_not_in.
  rewrite <- injected_family_off_CFG. exact (Hna x8 Hx).
Qed.

Lemma sstep_running : forall c e st, sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H. destruct H; cbn [cfg_model]; assumption. Qed.

Lemma star_cases : forall c tr c', star segs c tr c' ->
  c' = c \/ exists e c2 tr2, sstep segs c e (SNext c2) /\ star segs c2 tr2 c'.
Proof.
  intros c tr c' H. destruct H as [c0 | c1 e c2 tr2 c3 Hss Hstar].
  - left. reflexivity.
  - right. exists e, c2, tr2. split; [exact Hss | exact Hstar].
Qed.

(** A node with the check is not budget-refused. *)
Lemma node_not_refused : forall c I evs nx,
  node_ok segs c I evs nx -> sys_nonalloc segs c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ Hc] Hna [Hh Hb].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs.
    destruct (Hc [] SError (sstep_cfg_of_sstep segs _ [] SError Hna Hs)) as (i & _ & Hbad).
    discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hb.
  (* LPS 727298f3: the instruction arm of [budget_refused_at] gained the vDSO call whose
     syscall effect cannot be materialized ([Run.budget_fault_vdso_sstep_error]). *)
  destruct Hb as [(Hsvc & [(report & Hstep & Hmat)
                           | (Hunm & fn & n & eff & model' & evs' & Hfn & Hn & Hspec & Hret & Hh' & Hmat)])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr (budget_fault_vdso_sstep_error segs ms model fn n eff model' evs'
                   Hh Hsvc Hunm Hfn Hn Hspec Hret Hh' Hmat)).
  - pose proof (sys_nonalloc_budget (mkCfg ms model) x8 Hna Hx8) as Hg.
    cbn [cfg_ms cfg_model] in Hg. congruence.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma srz_star_not_refused : forall c T, srealizes c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hna Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hna).
    + destruct (proj2 Hnode e (SNext c2) (sstep_cfg_of_sstep segs c e (SNext c2) Hna Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + intros [Hn _]. exact (Hh Hn).
    + exfalso. exact (Hh (sstep_running c e _ Hss)).
  - exact (IH tr c' Hstar).
Qed.

(** No configuration the run reaches from an [srealizes] configuration is
    budget-refused. *)
Theorem srz_never_refused : forall c T, srealizes c T ->
  ~ reaches_budget_refused segs c.
Proof.
  intros c T H (tr & c' & Hstar & Hb). exact (srz_star_not_refused c T H tr c' Hstar Hb).
Qed.

(** ...and so under every spurious-failure configuration
    ([Run.reaches_budget_refused_cfg_sub]). *)
Theorem srz_never_refused_cfg : forall cfg c T, srealizes c T ->
  ~ reaches_budget_refused_cfg segs cfg c.
Proof.
  intros cfg c T H Hr. exact (srz_never_refused c T H (reaches_budget_refused_cfg_sub segs cfg c Hr)).
Qed.

(** ** The released node lemmas, with the check *)

Lemma srz_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  sys_nonalloc segs c ->
  RomBase.sys_rob segs c ->
  srealizes c' T ->
  srealizes c T.
Proof.
  intros c c' T Hnode Hna Hrob Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hna Hrob).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.

Lemma srz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  sys_nonalloc segs c ->
  RomBase.sys_rob segs c ->
  (forall i, srealizes (nx (inl i)) A) ->
  (forall i, srealizes (nx (inr i)) B) ->
  srealizes c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode Hna Hrob HA HB.
  assert (HA0 : A []) by (eapply srealizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
  apply (srz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end)
             (inl a0) Hnode Hna Hrob).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(** An instruction step has no pending call, so it needs no new premise. *)
Lemma srz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply srz_silent1;
    [apply node_instr; eassumption | apply sys_nonalloc_instr; exact Hsvc
    | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

Lemma srz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply srz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                   | apply IH; exact Hc].
Qed.

End WithSegs.

(** ** The run's segments (LPS 08b1429)

    The run reads the binary against [run_segments] (its segments and the vDSO pair) from the
    run's own start.  As [Common.Cfg.SRomStable.srun_init] does for the released relation, a
    walk over the binary's own segments lifts to that: first to the larger read-only backing
    ([srealizes_wrom]), then to the longer segment list ([srealizes_app_tail]).  The node
    facts come from [SRomStable]; the check [sys_nonalloc] reads only the syscall number, so it
    carries over unchanged ([sys_nonalloc_wrom], [sys_nonalloc_app]). *)

Lemma sys_nonalloc_wrom : forall segs c r,
  sys_nonalloc segs c -> sys_nonalloc segs (RomBase.cwrom c r).
Proof.
  intros segs [ms m] r Hna x8 Hx. pose proof (Hna x8 Hx) as E.
  unfold injected_family_off in *. cbn [sys_input in_sysno] in *. exact E.
Qed.

Lemma sys_nonalloc_app : forall segs tail c,
  sys_nonalloc segs c -> sys_nonalloc (segs ++ tail) c.
Proof.
  intros segs tail c Hna x8 Hx. pose proof (Hna x8 Hx) as E.
  unfold injected_family_off in *. cbn [sys_input in_sysno] in *. exact E.
Qed.

Theorem srealizes_wrom : forall segs, vdso_image segs = None ->
  forall c T, srealizes segs c T ->
  forall r, RomBase.rom_ext (ms_rom (cfg_ms c)) r -> srealizes segs (RomBase.cwrom c r) T.
Proof.
  intros segs Hvi c T H;
    induction H as [c I evs nx T i0 Hn Hna Hrob Hc IH | c Hh | c T T' H IH Heq]; intros r Hr.
  - apply (srz_node segs (RomBase.cwrom c r) I evs (fun i => RomBase.cwrom (nx i) r) T i0).
    + eapply SRomStable.node_wrom; eassumption.
    + exact (sys_nonalloc_wrom segs c r Hna).
    + eapply SRomStable.sys_rob_wrom; eassumption.
    + intros i. apply IH.
      replace (ms_rom (cfg_ms (nx i))) with (ms_rom (cfg_ms c)); [exact Hr|].
      symmetry. eapply SRomStable.node_rom; eassumption.
  - apply srz_halt. exact Hh.
  - eapply srz_conseq; [apply IH; exact Hr | exact Heq].
Qed.

Theorem srealizes_app_tail : forall segs tail,
  (forall s, In s tail -> seg_executable s = false) ->
  (forall s, In s tail -> seg_writable s = false) ->
  vdso_image segs = None ->
  forall c T, srealizes segs c T -> srealizes (segs ++ tail) c T.
Proof.
  intros segs tail Hnx Hnw Hvi c T H;
    induction H as [c I evs nx T i0 Hnode Hna Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - apply (srz_node (segs ++ tail) c I evs nx T i0).
    + eapply SRomStable.node_ok_app_tail; eassumption.
    + exact (sys_nonalloc_app segs tail c Hna).
    + eapply SRomStable.sys_rob_app_tail; eassumption.
    + exact IH.
  - exact (srz_halt (segs ++ tail) c Hh).
  - exact (srz_conseq (segs ++ tail) c T T' IH Heq).
Qed.

Theorem srealizes_run_segments : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  srealizes segs c T -> srealizes (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply (srealizes_app_tail segs _
           (fun s Hs => SRomStable.vdso_segments_nx _ _ _ s Hs)
           (fun s Hs => SRomStable.vdso_segments_nw _ _ _ s Hs) Hvi).
  exact H.
Qed.

(** A walk over the binary's own segments, from the binary's start, is one over the run's
    segments from the run's start. *)
Theorem srun_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  srealizes segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  srealizes (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite SRomStable.init_config_run_segments.
  apply srealizes_run_segments; [exact Hvi|].
  apply (srealizes_wrom segs Hvi); [exact H|].
  rewrite SRomStable.init_config_rom. apply SRomStable.rom_ext_run_segments.
Qed.
