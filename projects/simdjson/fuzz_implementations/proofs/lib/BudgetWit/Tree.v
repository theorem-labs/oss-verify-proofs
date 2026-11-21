(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Lib/ITree.v's run invariant (tree_at, impl_sstep_inv) and TopLevel.v's run_of_tree: a program tree with no allocation node never reaches a budget-refused configuration, under every spurious-failure configuration. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: nodes_sound is used over minvR with the channel-reader flag, budget refusal has a vDSO-call case, and the run is lifted to the binary's segments plus the vDSO segments; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/BudgetWit/Tree.v, 42 lines within its lines 38-209. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import MState Exec ITree Nodes RegsEquiv.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.BudgetWit Require Import Quiet.
Import ListNotations.

(** * The budget premise from a program tree with no allocation node

    [Lib.ITree] relates a program tree to the run by [impl] and [node_sound], and
    [Lib.Nodes.nodes_sound] instantiates [node_sound] at [ACFG] with the per-node
    side condition [nsafeU].  [nsafeQ] adds [Quiet.nalloc] to that side condition;
    since a side condition appears in [node_sound] only as a premise,
    [nodes_sound_q] follows from [nodes_sound].

    [Run.budget_refused_at] has three clauses.  The first (an instruction's first
    touch of a lazy mapping) needs [m_vm_lazy <> []], which [minv] excludes
    ([Nodes.minv_lazy]).  The second (the grant mark) and the third (a
    materialization fault of a syscall outcome the spec allows) need a pending call:
    there [tree_at] gives a node, [nalloc] makes the mark [false]
    ([Quiet.nalloc_quiet]), and the third clause is the premise of an [SError]
    step ([Run.budget_fault_syscall_sstep_error]), which is an [ACFG] step
    ([Quiet.sstep_cfg_quiet]) and so excluded by [ITree.impl_sstep_inv].

    The invariant [qinv] is carried along the UNFILTERED run ([Run.star]): each
    unfiltered step from a tree configuration is an [ACFG] step
    ([Quiet.sstep_cfg_quiet]).  So no configuration the unfiltered run reaches is
    budget-refused, and by [Run.reaches_budget_refused_cfg_sub] none that the run
    under any configuration reaches ([run_never_budget_refused]). *)

Definition nsafeQ (n : node) (mo : Model) : Prop := nsafeU n mo /\ nalloc n.

(* LPS 727298f3: [Nodes.nodes_sound] is stated over [minvR], [minv] with the
   channel-reader bit the hand-off reads ([Run.valid_input_either] pins it). *)
Lemma nodes_sound_q : forall segs,
  node_sound node segs ACFG (at_node segs) nstep nexit minvR nsafeQ.
Proof.
  intros segs. destruct (nodes_sound segs) as [Hl Hp Hc Hs Hx Hg].
  constructor.
  - exact Hl.
  - exact Hp.
  - intros n ms mo evs X Ha Hh Hm [Hn _]. exact (Hc n ms mo evs X Ha Hh Hm Hn).
  - intros n ms mo rsp mo' evs Ha Hh Hm [Hn _]. exact (Hs n ms mo rsp mo' evs Ha Hh Hm Hn).
  - intros n ms mo code mo' Ha Hh Hm [Hn _]. exact (Hx n ms mo code mo' Ha Hh Hm Hn).
  - intros n ms mo Ha Hh Hm [Hn _]. exact (Hg n ms mo Ha Hh Hm Hn).
Qed.

Section T.
Variable segs : list Segment.

Definition qinv {R} (Q : R -> machine_state -> Prop) (c : config) : Prop :=
  (exists t : itree node R, tree_at segs (at_node segs) nstep minvR nsafeQ t Q (cfg_ms c) (cfg_model c))
  \/ m_halted (cfg_model c) <> None.

(** A pending call at a tree configuration is the call of a node that is not an
    allocation call. *)
Lemma tree_at_quiet : forall {R} (t : itree node R) Q ms mo x8,
  tree_at segs (at_node segs) nstep minvR nsafeQ t Q ms mo ->
  ms_svc_pending ms = Some x8 ->
  injected_family_off ACFG (sys_input segs ms x8) = false /\
  alloc_budget_refused_b (sys_input segs ms x8) mo = false.
Proof.
  intros R t Q ms mo x8 (Ht & Hl & Hh & Hinv & Hsf & Hnc) Hx.
  destruct t as [r|n k|kc].
  - exfalso. exact (Hl [] r mo (conj eq_refl (conj eq_refl eq_refl))).
  - cbn in Ht. destruct Ht as (ms1 & Hm & Hat & _).
    destruct Hsf as [[_ Hq] _].
    inversion Hm; subst.
    + eapply nalloc_quiet; eassumption.
    + exfalso. match goal with H : mstep segs _ _ |- _ => destruct H as [Hn _] end. congruence.
  - destruct Hnc.
Qed.

(** Every unfiltered step from a configuration of [qinv] is an [ACFG] step, and
    leads to a configuration of [qinv]. *)
Lemma qinv_step : forall {R} (Q : R -> machine_state -> Prop) c evs c',
  qinv Q c -> sstep segs c evs (SNext c') -> qinv Q c'.
Proof.
  intros R Q [ms mo] evs c' [(t & HT)|Hh] Hss; cbn [cfg_ms cfg_model] in *.
  - assert (Hss' : sstep_cfg segs ACFG (mkCfg ms mo) evs (SNext c')).
    { apply sstep_cfg_quiet; [|exact Hss]. cbn [cfg_ms].
      intros x8 Hx. exact (proj1 (tree_at_quiet t Q ms mo x8 HT Hx)). }
    destruct (impl_sstep_inv _ _ _ _ _ _ _ _ (nodes_sound_q segs) t Q ms mo evs (SNext c') HT Hss')
      as [(ms' & E & _ & _ & HT')|[(n & k & rsp & mo' & _ & _ & E & _ & HT')
         |(n & k & code & mo' & _ & _ & E & _ & _ & Hh')]];
      injection E as ->.
    + left. exists t. exact HT'.
    + left. exists (k rsp). exact HT'.
    + right. cbn [cfg_model]. congruence.
  - exfalso. inversion Hss; subst; congruence.
Qed.

(** No configuration of [qinv] is budget-refused. *)
Lemma qinv_not_refused : forall {R} (Q : R -> machine_state -> Prop) c,
  qinv Q c -> ~ budget_refused_at segs c.
Proof.
  intros R Q [ms mo] [(t & HT)|Hh] Hb; cbn [cfg_ms cfg_model] in *.
  - destruct (ms_svc_pending ms) as [x8|] eqn:Hx.
    + destruct (tree_at_quiet t Q ms mo x8 HT Hx) as [Hoff Hgr].
      destruct Hb as (Hh & [(Hn & _) | (y8 & Hy8 & [Hb | (eff & mo' & evs & Hspec & Hh' & Hmat)])]);
        cbn [cfg_ms cfg_model] in *.
      * congruence.
      * rewrite Hx in Hy8. injection Hy8 as <-. congruence.
      * rewrite Hx in Hy8. injection Hy8 as <-.
        pose proof (budget_fault_syscall_sstep_error segs ms mo x8 eff mo' evs Hh Hx Hspec Hh' Hmat) as Herr.
        assert (Herr' : sstep_cfg segs ACFG (mkCfg ms mo) [] SError).
        { apply sstep_cfg_quiet; [|exact Herr]. cbn [cfg_ms].
          intros z Hz. rewrite Hx in Hz. injection Hz as <-. exact Hoff. }
        destruct (impl_sstep_inv _ _ _ _ _ _ _ _ (nodes_sound_q segs) t Q ms mo [] SError HT Herr')
          as [(ms' & E & _)|[(n & k & rsp & mo'' & _ & _ & E & _)|(n & k & code & mo'' & _ & _ & E & _)]];
          discriminate E.
    + destruct HT as (_ & _ & _ & Hinv & _).
      exact (budget_refused_at_no_lazy_instr segs ms mo (minv_lazy mo (proj1 Hinv)) Hx Hb).
  - destruct Hb as [Hn _]. exact (Hh Hn).
Qed.

(** The itree analogue of libreac/fuzz_knock's [BudgetWit.Rzb.rzb_never_refused]: from a tree
    configuration whose tree has no allocation node, no configuration the
    unfiltered run reaches is budget-refused. *)
Theorem tree_never_budget_refused : forall {R} (t : itree node R) Q ms mo,
  impl segs (at_node segs) t Q ms ->
  leaves_unreachable_m nstep t mo ->
  m_halted mo = None -> minvR mo ->
  tsafe nstep nsafeQ t mo ->
  forall tr c, star segs (mkCfg ms mo) tr c -> ~ budget_refused_at segs c.
Proof.
  intros R t Q ms mo Ht0 Hl0 Hh Hinv Hs0 tr c Hstar.
  assert (Hres : exists t', resolves t' t /\ impl segs (at_node segs) t' Q ms)
    by (eapply impl_resolve; exact Ht0).
  destruct Hres as (t' & Hr & Ht).
  assert (H0 : qinv Q (mkCfg ms mo)).
  { left. exists t'. cbn [cfg_ms cfg_model].
    split; [exact Ht|]. split; [eapply leaves_unreachable_m_resolves; eassumption|].
    split; [exact Hh|]. split; [exact Hinv|]. split; [eapply tsafe_resolves; eassumption|].
    eapply resolves_nocho; eassumption. }
  exact (qinv_not_refused Q c
           (star_invariant segs (qinv Q) (fun c1 evs c2 H1 H2 => qinv_step Q c1 evs c2 H1 H2)
              (mkCfg ms mo) tr c Hstar H0)).
Qed.

(** [budget_refused_at] reads the machine state only through fields [ms_eqv]
    keeps equal. *)
Lemma budget_refused_at_eqv : forall c c',
  cfg_eqv c c' -> budget_refused_at segs c -> budget_refused_at segs c'.
Proof.
  intros [ms mo] [ms' mo'] [Hms Hmo] Hb; cbn [cfg_ms cfg_model] in *; subst mo'.
  pose proof Hms as (_ & _ & Hpc & Hsvc & _).
  (* LPS 727298f3: [budget_refused_at]'s instruction arm has a second case, a
     vDSO call whose modeled syscall's accesses the budget refuses. *)
  destruct Hb as (Hh & [(Hn & [(report & Hst & Hmat)
                             | (Hu & fn & n & eff & mo'' & evs & Hfn & Hno & Hspec & Hret & Hh'' & Hmat)])
                       | (x8 & Hx8 & Hcl)]); cbn [cfg_ms cfg_model] in *.
  - split; [exact Hh|]. left. cbn [cfg_ms cfg_model]. split; [congruence|]. left.
    pose proof (step_accesses_eqv segs ms ms' Hms) as Ha. rewrite Hst in Ha.
    revert Ha. destruct (RiscvSemantics.step_accesses segs ms') eqn:E; cbn [ares_eqv]; intros Ha; try contradiction.
    match type of E with _ = MachineOk ?r => exists r end.
    split; [reflexivity|]. destruct Ha as [_ Hr]. rewrite <- Hr. exact Hmat.
  - split; [exact Hh|]. left. cbn [cfg_ms cfg_model]. split; [congruence|]. right. split.
    + pose proof (mi_account_step_eqv segs ms ms' mo Hms) as Ha. rewrite Hu in Ha.
      destruct (mi_account_step segs ms' mo); cbn in Ha; try contradiction; reflexivity.
    + exists fn, n, eff, mo'', evs.
      replace (ms_pc ms') with (ms_pc ms) by (unfold ms_pc; exact Hpc).
      rewrite <- (sys_input_eqv segs ms ms' (Z_to_bv 64 n) Hms). tauto.
  - split; [exact Hh|]. right. exists x8. cbn [cfg_ms cfg_model]. split; [congruence|].
    rewrite <- (sys_input_eqv segs ms ms' x8 Hms). exact Hcl.
Qed.
End T.

(** The run-level form, mirroring [TopLevel.run_of_tree]: for every
    spurious-failure configuration, the run of the image from the entry and the
    input is never budget-refused. *)
Theorem run_never_budget_refused : forall {R} segs pc ph lim en inp cfg (t : itree node R) Q,
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafeQ t (mo0 segs lim en inp) ->
  in_channel_reader inp = true ->
  ~ run_scfg_budget_refused cfg (mkImage segs pc ph) lim en inp.
Proof.
  intros R segs pc ph lim en inp cfg t Q Ht Hl Hs Hrd Hr.
  apply run_scfg_budget_refused_sub in Hr.
  destruct en as [sp brk mbase rnd].
  (* LPS 727298f3: the run reads every step against [run_segments segs inp sp mbase]
     = [segs ++ V], and [Run.init_machine_state] reads the whole launch input, the
     mmap base and the entry draw.  As in [TopLevel.run_of_tree], the tree is lifted
     to [segs ++ V] ([impl_lift]) and the ledger stays [segs]'s
     ([run_segments_reserved]). *)
  set (V := vdso_segments (in_kernel inp) sp mbase).
  assert (Hr' : reaches_budget_refused (segs ++ V)
            (mkCfg (init_machine_state (segs ++ V) pc ph sp mbase rnd inp)
                   (mo0 segs lim (mkEntry sp brk mbase rnd) inp))).
  { unfold mo0. cbn [en_sp en_mmap_base en_draw en_brk].
    rewrite <- (run_segments_reserved segs inp sp mbase). exact Hr. }
  destruct Hr' as (tr & c & Hstar & Hb).
  assert (Heq0 : cfg_eqv
    (mkCfg (init_machine_state (segs ++ V) pc ph sp mbase rnd inp)
           (mo0 segs lim (mkEntry sp brk mbase rnd) inp))
    (mkCfg (init_ms (segs ++ V) pc ph sp mbase rnd inp) (mo0 segs lim (mkEntry sp brk mbase rnd) inp))).
  { split; [exact (init_machine_state_eqv (segs ++ V) pc ph sp mbase rnd inp)
           | reflexivity]. }
  destruct (star_eqv (segs ++ V) _ tr c Hstar _ Heq0) as (c' & Hstar' & Hc).
  pose proof (impl_lift segs V t Q (ms0 segs pc ph (mkEntry sp brk mbase rnd) inp) (vdso_nonexec _ _ _) Ht) as Ht'.
  rewrite set_rom_ms0 in Ht'. cbn [en_sp en_mmap_base en_draw] in Ht'.
  exact (tree_never_budget_refused (segs ++ V) t _ _ _ Ht' Hl (mo0_not_halted _ _ _ _) (mo0_minvR _ _ _ _ Hrd) Hs
           tr c' Hstar' (budget_refused_at_eqv (segs ++ V) c c' Hc Hb)).
Qed.
