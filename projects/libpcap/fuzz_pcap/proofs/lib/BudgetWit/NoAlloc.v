(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from E2/Lib/ITree.v's run invariant (tree_at, impl_sstep_inv) and E2/Lib/Nodes.v's nodes_sound: a tree whose nodes make no allocation call proves the budget premise of every run it describes. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: munmap (215) is now one of the allocation-mark system calls (Run.alloc_mark_sysnos), in the comment and in the case split of the proof; and the lifting section takes the walk's peek function and its node_sound proof as parameters, so that a walk over the binary's segments, lifted onto the run's segments with the vDSO pair appended (RsLift.nodes_sound_rs), applies. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Exec ITree Nodes RegsEquiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import ExitBase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lim Require LimBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(** * A tree with no allocation node proves the budget premise

    The released proofs of this harness state each walk as [ITree.impl] over
    [Nodes.node]: the machine reaches, by instruction steps, the system call
    a node of a program tree names, and goes on from each response.
    [ITree.tree_at] adds that no leaf of the tree is reached, that the model
    satisfies [Nodes.minv] and that each node is safe, and
    [ITree.impl_sstep_inv] says what one step of the run does from a
    configuration a tree is at: an instruction step to a configuration the
    same tree is at, a node's response to one its subtree is at, or an exit.
    No [realizes] derivation is built on this path, so there is no carrier
    to add a grant check to.

    [budget_refused_at] (lps [Run.v]) is true at a running configuration in
    three cases: an instruction touches a lazy page the budget cannot back;
    the pending system call is a grant the budget refuses
    ([alloc_budget_refused_b]); or an outcome of the pending call touches such
    a page.  The first needs a lazy mapping, and [Nodes.minv] has none.  The
    second needs a call numbered 214, 215, 216, 222 or 226
    ([Run.alloc_mark_sysnos]).  The third is the premise of an error step,
    which [ITree.impl_sstep_inv] excludes at a tree's node.

    So the invariant here is [ITree.run_inv] with one more clause: every node
    of the tree at the configuration is one of [NWritev], [NWritevF],
    [NIoctl], [NSetTid], [NExit], [NLseek] ([nna], [tna]); these are system
    calls 66, 29, 96, 93 or 94, and 62.  [tree_never_refused] reads it over
    the unfiltered step [Run.sstep], so no configuration the run reaches is
    budget-refused under any spurious-failure configuration.  The node facts
    ([Nodes.nodes_sound]) are stated at [Nodes.CFG] = [alloc_only_cfg false];
    a step is moved there because on a call outside the allocation family the
    filter drops nothing ([AllocSim2__Common.ShapeAlg.sstep_cfg_of_unfiltered],
    [tree_unfiltered]), and the same fact rules out a refused grant.  The
    invariant also carries a register equivalence ([RegsEquiv.ms_eqv]),
    because the released tree starts at [RegsEquiv.init_ms] and the run at
    [Run.init_machine_state].

    The six nodes neither read nor change the limit, so their tree's leaves
    are unreachable, and the tree is safe, at any limit when they are at one
    ([leaves_setL], [tsafe_setL]). *)

(** The nodes on the usage path: writev (to a channel or a file),
    ioctl, set_tid_address, exit, lseek. *)
Definition nna (n : node) : bool :=
  match n with
  | NWritev _ _ | NWritevF _ _ | NIoctl _ _ | NSetTid | NExit _ | NLseek _ _ _ => true
  | _ => false
  end.

Definition NAn (n : node) : Prop := nna n = true.

(** Every node of the tree is one of them: [ExitBase.tall] at [NAn]. *)
Definition tna {R : Type} (t : itree node R) : Prop := tall NAn (fun _ : R => True) t.

Local Ltac not_alloc_lit :=
  let Hin := fresh "Hin" in
  intros Hin; vm_compute in Hin;
  repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin] end;
  first [discriminate Hin | exact Hin].

Lemma alloc_no_false : forall z, ~ In z alloc_mark_sysnos ->
  AllocSim2__Common.ShapeAlg.alloc_no z = false.
Proof.
  intros z Hz. unfold AllocSim2__Common.ShapeAlg.alloc_no.
  destruct (Z.eqb_spec 214 z) as [<-|_]; [exfalso; apply Hz; unfold alloc_mark_sysnos; cbn; auto|].
  destruct (Z.eqb_spec 215 z) as [<-|_]; [exfalso; apply Hz; unfold alloc_mark_sysnos; cbn; auto|].
  destruct (Z.eqb_spec 216 z) as [<-|_]; [exfalso; apply Hz; unfold alloc_mark_sysnos; cbn; auto|].
  destruct (Z.eqb_spec 222 z) as [<-|_]; [exfalso; apply Hz; unfold alloc_mark_sysnos; cbn; auto|].
  destruct (Z.eqb_spec 226 z) as [<-|_]; [exfalso; apply Hz; unfold alloc_mark_sysnos; cbn; auto 7|].
  reflexivity.
Qed.

(** ** The six nodes do not read or change the limit *)

Lemma fds_setL : forall L m, m_fds (LimBase.setL L m) = m_fds m.
Proof. reflexivity. Qed.
Lemma fs_setL : forall L m, m_fs (LimBase.setL L m) = m_fs m.
Proof. reflexivity. Qed.
Lemma tid_setL : forall L m, m_tid (LimBase.setL L m) = m_tid m.
Proof. reflexivity. Qed.

(** After the matches on the descriptor table and the file system are
    split, each case is [False], or a response with the post-model [mo'] or
    a model built from [mo] by [with_fds] and [with_fs], which commute with
    [LimBase.setL]. *)
Local Ltac setL_cases :=
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
  first [ let Hr := fresh "Hr" in intros [Hr ->]; split; [exact Hr | reflexivity]
        | intros [] ].

Lemma nstep_setL : forall n mo rsp mo' evs L, nna n = true ->
  nstep n mo rsp mo' evs -> nstep n (LimBase.setL L mo) rsp (LimBase.setL L mo') evs.
Proof.
  intros n mo rsp mo' evs L Hn H.
  destruct n; cbn [nna] in Hn; try discriminate Hn; cbn [nstep] in H |- *.
  - (* NWritev *)
    unfold write_result in H |- *. destruct H as [-> H]. split; [reflexivity | exact H].
  - (* NIoctl *)
    rewrite fds_setL. destruct H as (He & -> & Hf). split; [exact He | split; [reflexivity | exact Hf]].
  - (* NSetTid *)
    rewrite tid_setL. destruct H as (He & t & Ht & H). split; [exact He|]. exists t. split; [exact Ht|].
    revert H. destruct (m_tid mo) as [t0|]; intros [H1 ->]; (split; [exact H1 | reflexivity]).
  - (* NExit *)
    exact H.
  - (* NWritevF *)
    rewrite ?fds_setL, ?fs_setL. destruct H as [He H]. split; [exact He|]. revert H. setL_cases.
  - (* NLseek *)
    unfold lseek_result in H |- *. rewrite ?fds_setL, ?fs_setL.
    destruct H as [He H]. split; [exact He|]. revert H. setL_cases.
Qed.

Lemma nsafe_setL : forall n mo L, nna n = true -> nsafe n (LimBase.setL L mo) -> nsafe n mo.
Proof. intros n mo L Hn H. destruct n; cbn [nna] in Hn; try discriminate Hn; exact H. Qed.

Lemma tpath_setL : forall R (t : itree node R) mo tr r mo' L, tna t ->
  tpath nstep t mo tr r mo' -> tpath nstep t (LimBase.setL L mo) tr r (LimBase.setL L mo').
Proof.
  intros R t. induction t as [r0|n k IH]; intros mo tr r mo' L Hna Hp; cbn [tpath] in *.
  - destruct Hp as (-> & -> & ->). split; [reflexivity | split; reflexivity].
  - unfold tna in Hna. cbn [tall] in Hna. destruct Hna as [Hn Hk].
    destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & ->).
    exists rsp, (LimBase.setL L mo1), evs, tr'.
    split; [exact (nstep_setL n mo rsp mo1 evs L Hn Hst)|].
    split; [exact (IH rsp mo1 tr' r mo' L (Hk rsp) Hp) | reflexivity].
Qed.

(** A path of the tree at [mo] is a path at [setL L mo], so the leaves are
    unreachable at [mo] when they are at [setL L mo]. *)
Lemma leaves_setL : forall R (t : itree node R) mo L, tna t ->
  leaves_unreachable_m nstep t (LimBase.setL L mo) -> leaves_unreachable_m nstep t mo.
Proof.
  intros R t mo L Hna Hl tr r mo' Hp.
  exact (Hl tr r (LimBase.setL L mo') (tpath_setL R t mo tr r mo' L Hna Hp)).
Qed.

(** ...and the tree is safe at [mo] when it is at [setL L mo]. *)
Lemma tsafe_setL : forall R (t : itree node R) mo L, tna t ->
  tsafe nstep nsafe t (LimBase.setL L mo) -> tsafe nstep nsafe t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo L Hna Hs; cbn [tsafe] in *; [exact I|].
  unfold tna in Hna. cbn [tall] in Hna. destruct Hna as [Hn Hk]. destruct Hs as [Hs0 Hs1]. split.
  - exact (nsafe_setL n mo L Hn Hs0).
  - intros rsp mo' evs Hst. apply (IH rsp mo' L (Hk rsp)).
    exact (Hs1 rsp (LimBase.setL L mo') evs (nstep_setL n mo rsp mo' evs L Hn Hst)).
Qed.

(** [TopLevel.mo0] at one limit is [mo0] at another with the limit set. *)
Lemma mo0_setL : forall segs L lim en inp, LimBase.setL L (mo0 segs lim en inp) = mo0 segs L en inp.
Proof. intros segs L lim [sp brk mb rnd] inp. reflexivity. Qed.

(** A tree that peels to another keeps [tna]. *)
Lemma peels_na : forall R mo (t t' : itree node R), peels nstep mo t t' -> tna t -> tna t'.
Proof.
  intros R mo t t' Hp. induction Hp as [t0|n0 k0 rsp t1 Hst Hp IH]; intros Hna; [exact Hna|].
  apply IH. unfold tna in Hna |- *. cbn [tall] in Hna. exact (proj2 Hna rsp).
Qed.

Section Lift.
Variable segs : list Segment.
(* The walk's peek function and its soundness: [Nodes.npeek segs] with [Nodes.nodes_sound segs], or, for a walk over
   the binary's segments lifted onto the run's ([RsLift.impl_rs_nodes]), [Nodes.npeek] of the binary's segments with
   [RsLift.nodes_sound_rs]. *)
Variable pk : node -> option (machine_state -> resp).
Hypothesis NS : node_sound node segs CFG (at_node segs) pk nstep nexit minv nsafe.

Lemma at_node_na : forall n ms x8, nna n = true -> at_node segs n ms ->
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros n ms x8 Hn Hat Hx.
  destruct n; cbn [nna] in Hn; try discriminate Hn; cbn [at_node] in Hat;
  repeat match type of Hat with _ /\ _ => destruct Hat as [Hat _] end;
  lazymatch type of Hat with
  | _ \/ _ => destruct Hat as [Hat|Hat]; rewrite Hat in Hx; injection Hx as <-; not_alloc_lit
  | _ => rewrite Hat in Hx; injection Hx as <-; not_alloc_lit
  end.
Qed.

Lemma sstep_live : forall c e st, sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H. destruct H; cbn [cfg_model]; assumption. Qed.

Lemma msteps_cases : forall ms ms1, msteps segs ms ms1 ->
  ms1 = ms \/ exists ms2, mstep segs ms ms2 /\ msteps segs ms2 ms1.
Proof.
  intros ms ms1 H. destruct H as [ms0 | ms0 ms2 ms3 Hs Hr];
    [left; reflexivity | right; exists ms2; split; assumption].
Qed.

(** At a configuration a tree is at, a pending call is the call of the
    tree's first node that is not a peek ([ITree.tree_at_inv]). *)
Lemma tree_pending_na : forall R (t : itree node R) Q ms mo x8,
  tree_at segs (at_node segs) pk nstep minv nsafe t Q ms mo -> tna t ->
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros R t Q ms mo x8 HT Hna Hx.
  destruct (tree_at_inv node segs CFG (at_node segs) pk nstep nexit minv nsafe NS
              t Q ms mo HT) as (n & k & ms1 & _ & Hp & Hm & Hat & _).
  pose proof (peels_na R mo t (Vis n k) Hp Hna) as Hn. unfold tna in Hn. cbn [tall] in Hn.
  destruct (msteps_cases ms ms1 Hm) as [-> | (ms2 & Hs & _)].
  - exact (at_node_na n ms x8 (proj1 Hn) Hat Hx).
  - exfalso. destruct Hs as [Hs _]. congruence.
Qed.

(** So the filter of [Nodes.CFG] drops no step there. *)
Lemma tree_unfiltered : forall R (t : itree node R) Q ms0 ms mo,
  ms_eqv ms ms0 -> tree_at segs (at_node segs) pk nstep minv nsafe t Q ms0 mo -> tna t ->
  AllocSim2__Common.ShapeAlg.unfiltered (mkCfg ms mo).
Proof.
  intros R t Q ms0 ms mo Heqv HT Hna x8 Hx. cbn [cfg_ms] in Hx.
  apply alloc_no_false.
  pose proof Heqv as (_ & _ & _ & Hsvc & _).
  apply (tree_pending_na R t Q ms0 mo x8 HT Hna). rewrite <- Hsvc. exact Hx.
Qed.

(** [ITree.run_inv], with the tree's nodes outside the allocation family and
    the machine state up to [RegsEquiv.ms_eqv]. *)
Definition Inv_na {R : Type} (Q : R -> machine_state -> Prop) (c : config) : Prop :=
  m_halted (cfg_model c) <> None \/
  exists (t : itree node R) ms0, ms_eqv (cfg_ms c) ms0 /\
    tree_at segs (at_node segs) pk nstep minv nsafe t Q ms0 (cfg_model c) /\ tna t.

Lemma Inv_na_step : forall R Q c evs c', Inv_na (R:=R) Q c -> sstep segs c evs (SNext c') -> Inv_na Q c'.
Proof.
  intros R Q [ms mo] evs c' HI Hss.
  destruct HI as [Hh | (t & ms0 & Heqv & HT & Hna)]; cbn [cfg_ms cfg_model] in *.
  - exfalso. apply Hh. exact (sstep_live _ _ _ Hss).
  - pose proof (AllocSim2__Common.ShapeAlg.sstep_cfg_of_unfiltered segs _ _ _
                  (tree_unfiltered R t Q ms0 ms mo Heqv HT Hna) Hss) as Hcfg.
    destruct (sstepC_eqv segs CFG ms ms0 mo evs (SNext c') Heqv Hcfg) as (X' & Hss0 & HX).
    destruct (tree_at_inv node segs CFG (at_node segs) pk nstep nexit minv nsafe NS
                t Q ms0 mo HT) as (n & k & _ & Hn & Hp & _ & _ & _ & HT0).
    pose proof (peels_na R mo t (Vis n k) Hp Hna) as Hna0.
    destruct (impl_sstep_inv node segs CFG (at_node segs) pk nstep nexit minv nsafe NS
                n k Q ms0 mo evs X' Hn HT0 Hss0)
      as [(ms1 & -> & _ & _ & HT1) | [(rsp & mo1 & _ & -> & _ & HT1) | (code & mo1 & _ & -> & _ & _ & Hh1)]];
      destruct HX as [He Hm]; cbn [cfg_ms cfg_model] in He, Hm.
    + right. exists (Vis n k), ms1. rewrite Hm. split; [exact He|]. split; [exact HT1 | exact Hna0].
    + right. exists (k rsp), (nret ms0 rsp). rewrite Hm. split; [exact He|]. split; [exact HT1|].
      unfold tna in Hna0 |- *. cbn [tall] in Hna0. exact (proj2 Hna0 rsp).
    + left. rewrite Hm. rewrite Hh1. discriminate.
Qed.

Lemma Inv_na_not_refused : forall R Q c, Inv_na (R:=R) Q c -> ~ budget_refused_at segs c.
Proof.
  intros R Q [ms mo] HI Hb.
  destruct HI as [Hh | (t & ms0 & Heqv & HT & Hna)]; cbn [cfg_ms cfg_model] in *.
  - apply Hh. exact (proj1 Hb).
  - pose proof HT as (_ & _ & Hh & Hinv & _).
    pose proof (minv_nolazy mo Hinv) as Hlz.
    pose proof Heqv as (_ & _ & _ & Hsvc & _).
    pose proof Hb as Hb0.
    destruct Hb as (_ & [(Hnone & _) | (x8 & Hx & [Hg | (eff & mo' & e & Hsp & Hh' & Hm)])]);
      cbn [cfg_ms cfg_model] in *.
    + exact (budget_refused_at_no_lazy_instr segs ms mo Hlz Hnone Hb0).
    + assert (Hx0 : ms_svc_pending ms0 = Some x8) by (rewrite <- Hsvc; exact Hx).
      pose proof (alloc_budget_refused_b_outside (sys_input segs ms x8) mo
                    (tree_pending_na R t Q ms0 mo x8 HT Hna Hx0)) as Hf.
      change (alloc_budget_refused_b (sys_input segs ms x8) mo = true) in Hg. congruence.
    + pose proof (budget_fault_syscall_sstep_error segs ms mo x8 eff mo' e Hh Hx Hsp Hh' Hm) as Herr.
      pose proof (AllocSim2__Common.ShapeAlg.sstep_cfg_of_unfiltered segs _ _ _
                    (tree_unfiltered R t Q ms0 ms mo Heqv HT Hna) Herr) as Hcfg.
      destruct (sstepC_eqv segs CFG ms ms0 mo [] SError Heqv Hcfg) as (X' & Hss0 & HX).
      destruct (tree_at_inv node segs CFG (at_node segs) pk nstep nexit minv nsafe NS
                  t Q ms0 mo HT) as (n & k & _ & Hn & _ & _ & _ & _ & HT0).
      destruct (impl_sstep_inv node segs CFG (at_node segs) pk nstep nexit minv nsafe NS
                  n k Q ms0 mo [] X' Hn HT0 Hss0)
        as [(? & E & _) | [(? & ? & _ & E & _) | (? & ? & _ & E & _)]];
        rewrite E in HX; exact HX.
Qed.

(** A run that starts, up to [ms_eqv], where a tree with no allocation node
    is, never reaches a budget-refused configuration (unfiltered step). *)
Theorem tree_never_refused : forall R (t : itree node R) Q ms0 ms mo,
  ms_eqv ms ms0 -> tree_at segs (at_node segs) pk nstep minv nsafe t Q ms0 mo -> tna t ->
  ~ reaches_budget_refused segs (mkCfg ms mo).
Proof.
  intros R t Q ms0 ms mo Heqv HT Hna.
  apply (never_budget_refused_ind segs (Inv_na (R:=R) Q)).
  - right. exists t, ms0. split; [exact Heqv | split; [exact HT | exact Hna]].
  - intros c e c' HI Hs. exact (Inv_na_step R Q c e c' HI Hs).
  - intros c HI. exact (Inv_na_not_refused R Q c HI).
Qed.

End Lift.
