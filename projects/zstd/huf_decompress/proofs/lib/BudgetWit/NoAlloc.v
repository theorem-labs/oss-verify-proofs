(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Lib/ITree.v, Lib/Cfg.v and Spec/StepB.v: a tree whose nodes make no allocation call proves the budget premise of every run it describes. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Exec Cfg ITree Nodes RegsEquiv.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import StepB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(** * A tree with no allocation node proves the budget premise

    The released proofs of this harness state the plain build's run as
    [ITree.impl]: the machine reaches, by instruction steps, the system call
    that a node of a program tree names, and goes on from each response.
    [Nodes.nodes_sound] says that at a node the step [Run.sstep_cfg] at
    [Cfg.ACFG] takes exactly the node's responses ([ns_complete]), and
    [ITree.impl_sstep_inv] turns that into the step of a run invariant.

    [budget_refused_at] (lps [Run.v]) is true at a running configuration in
    three cases: an instruction touches a lazy page the budget cannot back;
    the pending system call is a grant the budget refuses
    ([alloc_budget_refused_b]); or an outcome of the pending call touches such
    a page.  The first needs a lazy mapping, and [Nodes.minv] has none
    ([ns_nolazy]).  The second needs a call numbered 214, 216, 222 or 226
    ([Run.alloc_mark_sysnos]).  The third is the premise of an error step,
    which the run invariant excludes.

    The budget premise is stated over the unfiltered step [Run.sstep], and
    [ns_complete] over the filtered one.  The node premise below closes that
    gap as well: at a configuration whose pending call is not numbered 214,
    216, 222 or 226, or that has no pending call, every unfiltered step is a
    step at [ACFG] ([Cfg.transparent_nonalloc], [Cfg.transparent_instr]).

    [tna t] says every node of [t] is one of [NWritev], [NIoctl], [NSetTid],
    [NExit] ([nna]); these are system calls 66, 29, 96 and 93 or 94.  The
    invariant [Inv_na] is: the process has halted, or such a tree is at the
    configuration up to [RegsEquiv.ms_eqv] (the released trees start at
    [InitMem.init_ms], the run at [Run.init_machine_state]).
    [tree_never_refused] reads the invariant over the unfiltered step, so no
    configuration the run reaches is budget-refused under any
    spurious-failure configuration.  [tnf_tna] gives the released model
    proof's never-forced premise [StepB.tnf] for such a tree at every limit. *)

(** The nodes on the usage path: writev, ioctl, set_tid_address, exit. *)
Definition nna (n : node) : bool :=
  match n with
  | NWritev _ _ | NIoctl _ _ | NSetTid | NExit _ => true
  | _ => false
  end.

(** Every node of the tree is one of them. *)
Fixpoint tna {R : Type} (t : itree node R) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => nna n = true /\ forall rsp, tna (k rsp)
  end.

Lemma tna_ebind : forall A B (t : itree node (Exc.exc A)) (f : A -> itree node (Exc.exc B)),
  tna t -> (forall a, tna (f a)) -> tna (ebind t f).
Proof.
  intros A B t f. induction t as [r|n k IH]; intros Ht Hf.
  - destruct r as [|a]; [exact I | exact (Hf a)].
  - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. exact (IH rsp (Hk rsp) Hf).
Qed.

(** Such a tree is never forced, at every model: [StepB.NF] is [True] off
    [NMmap] and [NMprotect]. *)
Lemma tnf_tna : forall R (t : itree node R) mo, tna t -> tnf t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo Hna; [exact I|].
  destruct Hna as [Hn Hk]. split.
  - destruct n; cbn [nna] in Hn; try discriminate Hn; exact I.
  - intros rsp mo' evs _. exact (IH rsp mo' (Hk rsp)).
Qed.

Local Ltac not_alloc_lit :=
  let Hin := fresh "Hin" in
  intros Hin; vm_compute in Hin;
  repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin] end;
  first [discriminate Hin | exact Hin].

Section Lift.
Variable segs : list Segment.

Local Notation tat := (tree_at segs (at_node segs) nstep minv nsafe).

Lemma at_node_na : forall n ms x8, at_node segs n ms -> nna n = true ->
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros n ms x8 Hat Hn Hx.
  destruct n; cbn [nna] in Hn; try discriminate Hn; cbn [at_node] in Hat;
  repeat match type of Hat with _ /\ _ => destruct Hat as [Hat _] end;
  lazymatch type of Hat with
  | _ \/ _ => destruct Hat as [Hat|Hat]; rewrite Hat in Hx; injection Hx as <-; not_alloc_lit
  | _ => rewrite Hat in Hx; injection Hx as <-; not_alloc_lit
  end.
Qed.

Lemma sstep_live : forall c e st, sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H. inversion H; subst; cbn [cfg_model]; assumption. Qed.

Lemma msteps_cases : forall ms ms1, msteps segs ms ms1 ->
  ms1 = ms \/ exists ms2, mstep segs ms ms2 /\ msteps segs ms2 ms1.
Proof.
  intros ms ms1 H. destruct H as [ms0 | ms0 ms2 ms3 Hs Hr];
    [left; reflexivity | right; exists ms2; split; assumption].
Qed.

(** At a configuration a tree is at, a pending call is a node of the tree. *)
Lemma tree_na : forall R (t : itree node R) Q ms mo x8,
  tat t Q ms mo -> tna t ->
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros R t Q ms mo x8 (Ht & Hl & _) Hna Hx.
  destruct t as [r|n k].
  - exfalso. apply (Hl [] r mo). cbn [tpath]. split; [reflexivity | split; reflexivity].
  - cbn [impl] in Ht. destruct Ht as (ms1 & Hm & Hat & _).
    destruct (msteps_cases ms ms1 Hm) as [-> | (ms2 & Hs1 & _)].
    + destruct Hna as [Hn _]. exact (at_node_na n ms x8 Hat Hn Hx).
    + exfalso. destruct Hs1 as [Hn _]. congruence.
Qed.

(** ...so every unfiltered step from it is a step at [ACFG]. *)
Lemma tat_transparent : forall R (t : itree node R) Q ms mo,
  tat t Q ms mo -> tna t -> cfg_transparent segs (mkCfg ms mo).
Proof.
  intros R t Q ms mo HT Hna.
  destruct (ms_svc_pending ms) as [x8|] eqn:Hx.
  - exact (transparent_nonalloc segs ms mo x8 Hx (tree_na R t Q ms mo x8 HT Hna Hx)).
  - exact (transparent_instr segs ms mo Hx).
Qed.

(** An unfiltered step from a configuration a tree is at reaches a
    configuration that has halted or that a subtree is at
    ([ITree.impl_sstep_inv]). *)
Lemma tat_step : forall R (t : itree node R) Q ms mo evs X,
  tat t Q ms mo -> tna t -> sstep segs (mkCfg ms mo) evs X ->
  exists c', X = SNext c' /\
    (m_halted (cfg_model c') <> None \/
     exists t' : itree node R, tat t' Q (cfg_ms c') (cfg_model c') /\ tna t').
Proof.
  intros R t Q ms mo evs X HT Hna Hss.
  pose proof (tat_transparent R t Q ms mo HT Hna evs X Hss) as Hc.
  destruct (impl_sstep_inv node segs (at_node segs) nstep nexit minv nsafe (nodes_sound segs)
              t Q ms mo evs X HT Hc)
    as [(ms' & -> & _ & _ & HT')
       |[(n & k & rsp & mo' & -> & _ & -> & _ & HT')
        |(n & k & code & mo' & -> & _ & -> & _ & _ & Hh')]].
  - eexists; split; [reflexivity|]. right. exists t. split; [exact HT' | exact Hna].
  - eexists; split; [reflexivity|]. right. exists (k rsp).
    cbn [tna] in Hna. split; [exact HT' | exact (proj2 Hna rsp)].
  - eexists; split; [reflexivity|]. left. cbn [cfg_model]. rewrite Hh'. discriminate.
Qed.

Definition Inv_na {R : Type} (Q : R -> machine_state -> Prop) (c : config) : Prop :=
  m_halted (cfg_model c) <> None \/
  exists (t : itree node R) ms0, ms_eqv (cfg_ms c) ms0 /\ tat t Q ms0 (cfg_model c) /\ tna t.

Lemma Inv_na_step : forall R Q c evs c', Inv_na (R:=R) Q c -> sstep segs c evs (SNext c') -> Inv_na Q c'.
Proof.
  intros R Q [ms mo] evs c' HI Hss.
  destruct HI as [Hh | (t & ms0 & Heqv & HT & Hna)]; cbn [cfg_ms cfg_model] in *.
  - exfalso. apply Hh. exact (sstep_live _ _ _ Hss).
  - destruct (sstep_eqv segs ms ms0 mo evs (SNext c') Heqv Hss) as (X' & Hss0 & HX).
    destruct (tat_step R t Q ms0 mo evs X' HT Hna Hss0) as (c0 & -> & Hc0).
    destruct HX as [He Hm].
    destruct Hc0 as [Hh0 | (t' & HT' & Hna')].
    + left. rewrite Hm. exact Hh0.
    + right. exists t', (cfg_ms c0). rewrite Hm. split; [exact He | split; [exact HT' | exact Hna']].
Qed.

Lemma Inv_na_not_refused : forall R Q c, Inv_na (R:=R) Q c -> ~ budget_refused_at segs c.
Proof.
  intros R Q [ms mo] HI Hb.
  destruct HI as [Hh | (t & ms0 & Heqv & HT & Hna)]; cbn [cfg_ms cfg_model] in *.
  - apply Hh. exact (proj1 Hb).
  - pose proof HT as (_ & _ & Hh & Hinv & _).
    pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound segs) mo Hinv) as Hlz.
    pose proof Heqv as (_ & _ & _ & Hsvc & _).
    pose proof Hb as Hb0.
    destruct Hb as (_ & [(Hnone & _) | (x8 & Hx & [Hg | (eff & mo' & e & Hsp & Hh' & Hm)])]);
      cbn [cfg_ms cfg_model] in *.
    + exact (budget_refused_at_no_lazy_instr segs ms mo Hlz Hnone Hb0).
    + assert (Hx0 : ms_svc_pending ms0 = Some x8) by (rewrite <- Hsvc; exact Hx).
      pose proof (alloc_budget_refused_b_outside (sys_input segs ms x8) mo (tree_na R t Q ms0 mo x8 HT Hna Hx0)) as Hf.
      change (alloc_budget_refused_b (sys_input segs ms x8) mo = true) in Hg. congruence.
    + assert (Hx0 : ms_svc_pending ms0 = Some x8) by (rewrite <- Hsvc; exact Hx).
      rewrite (sys_input_eqv segs ms ms0 x8 Heqv) in Hsp.
      pose proof (budget_fault_syscall_sstep_error segs ms0 mo x8 eff mo' e Hh Hx0 Hsp Hh' Hm) as Herr.
      destruct (tat_step R t Q ms0 mo [] SError HT Hna Herr) as (c0 & E & _). discriminate E.
Qed.

(** A run that starts, up to [ms_eqv], where a tree with no allocation node
    is, never reaches a budget-refused configuration (unfiltered step). *)
Theorem tree_never_refused : forall R (t : itree node R) Q ms0 ms mo,
  ms_eqv ms ms0 -> tat t Q ms0 mo -> tna t ->
  ~ reaches_budget_refused segs (mkCfg ms mo).
Proof.
  intros R t Q ms0 ms mo Heqv HT Hna.
  apply (never_budget_refused_ind segs (Inv_na (R:=R) Q)).
  - right. exists t, ms0. split; [exact Heqv | split; [exact HT | exact Hna]].
  - intros c e c' HI Hs. exact (Inv_na_step R Q c e c' HI Hs).
  - intros c HI. exact (Inv_na_not_refused R Q c HI).
Qed.

End Lift.
