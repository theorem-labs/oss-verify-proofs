(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Lib/ITree.v and Lib/ITreeCfg.v: a tree whose nodes make no allocation call proves the budget premise of every run it describes. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes RegsEquiv NodesCfg NodesCfgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(** * A tree with no allocation node proves the budget premise

    The released proofs of this harness state each walk as [ITree.impl]: the
    machine reaches, by instruction steps, the system call that a node of a
    program tree names (or a branch of a [Choice]), and goes on from each
    response.  [Nodes.nodes_sound] says that at a node the unfiltered step
    [Run.sstep] takes exactly the node's responses ([ns_complete]).  The
    plain lane turns the tree into a [realizes] derivation
    ([ITreeCfg.impl_realizes]), which records no system-call number, so there
    is no derivation to add a grant check to; this file reads the tree
    itself.

    [budget_refused_at] (lps [Run.v]) is true at a running configuration in
    three cases: an instruction touches a lazy page the budget cannot back;
    the pending system call is a grant the budget refuses
    ([alloc_budget_refused_b]); or an outcome of the pending call touches such
    a page.  The first needs a lazy mapping, and [Nodes.minv] has none.  The
    second needs a call numbered 214, 216, 222 or 226
    ([Run.alloc_mark_sysnos]).  The third is the premise of an error step,
    which [ns_complete] excludes at a node.

    [tat] is [ITreeCfg.tree_at] at the unfiltered node step [Nodes.nstep].
    The invariant [Inv_na] is: the process has halted, or such a tree is at
    the configuration up to [RegsEquiv.ms_eqv] (the released trees start at
    [RegsEquiv.init_ms], the run at [Run.init_machine_state]), and every node
    of it is one of [NWritev], [NIoctl], [NSetTid], [NExit] ([nna], [tna]);
    these are system calls 66, 29, 96 and 93 or 94.  [tat_step] is the step
    of [ITree.ITree]'s run invariant, by induction on the tree because of
    [Choice].  [tree_never_refused] reads the invariant over the unfiltered
    step, so no configuration the run reaches is budget-refused under any
    spurious-failure configuration.

    The released [ModelInv.prog_model_ok] states the tree's leaves and
    safety at the node step [NodesCfgA.nstep_a]; on the four nodes that step
    is [nstep] ([nstep_a_of_na]), so the leaves are unreachable at [nstep]
    too ([leaves_a_na]), and their safety condition is [True] ([tsafe_na]). *)

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
  | Choice _ k => forall a, tna (k a)
  end.

Lemma tna_ebind : forall A B (t : itree node (Exc.exc A)) (f : A -> itree node (Exc.exc B)),
  tna t -> (forall a, tna (f a)) -> tna (ebind t f).
Proof.
  intros A B t f. induction t as [r|n k IH|v k IH]; intros Ht Hf.
  - destruct r as [|a]; [exact I | exact (Hf a)].
  - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. exact (IH rsp (Hk rsp) Hf).
  - intros a. exact (IH a (Ht a) Hf).
Qed.

Local Ltac not_alloc_lit :=
  let Hin := fresh "Hin" in
  intros Hin; vm_compute in Hin;
  repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin] end;
  first [discriminate Hin | exact Hin].

Lemma nna_nonalloc : forall n, nna n = true -> node_alloc n = false.
Proof. intros n Hn. destruct n; cbn [nna] in Hn; try discriminate Hn; reflexivity. Qed.

(** On the four nodes, [NodesCfgA.nstep_a] is [Nodes.nstep]. *)
Lemma nstep_a_of_na : forall n mo rsp mo' evs, nna n = true ->
  nstep n mo rsp mo' evs -> nstep_a n mo rsp mo' evs.
Proof.
  intros n mo rsp mo' evs Hn H.
  split; [exact (nstep_c_of_nonalloc n mo rsp mo' evs (nna_nonalloc n Hn) H)|].
  destruct n; cbn [nna] in Hn; try discriminate Hn; exact I.
Qed.

Lemma tpath_a_of_na : forall R (t : itree node R) mo tr r mo', tna t ->
  tpath nstep t mo tr r mo' -> tpath nstep_a t mo tr r mo'.
Proof.
  intros R t. induction t as [r0|n k IH|v k IH]; intros mo tr r mo' Hna Hp; cbn [tpath] in *.
  - exact Hp.
  - destruct Hna as [Hn Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & ->).
    exists rsp, mo1, evs, tr'.
    split; [exact (nstep_a_of_na n mo rsp mo1 evs Hn Hst)|].
    split; [exact (IH rsp mo1 tr' r mo' (Hk rsp) Hp) | reflexivity].
  - destruct Hp as (a & Hv & Hp). exists a. split; [exact Hv | exact (IH a mo tr r mo' (Hna a) Hp)].
Qed.

Lemma leaves_a_na : forall R (t : itree node R) mo, tna t ->
  leaves_unreachable_m nstep_a t mo -> leaves_unreachable_m nstep t mo.
Proof.
  intros R t mo Hna Hl tr r mo' Hp. exact (Hl tr r mo' (tpath_a_of_na R t mo tr r mo' Hna Hp)).
Qed.

Lemma tsafe_na : forall R (t : itree node R) mo, tna t -> tsafe nstep nsafe t mo.
Proof.
  intros R t. induction t as [r|n k IH|v k IH]; intros mo Hna; cbn [tsafe]; [exact I| |].
  - destruct Hna as [Hn Hk]. split.
    + destruct n; cbn [nna] in Hn; try discriminate Hn; exact I.
    + intros rsp mo' evs _. exact (IH rsp mo' (Hk rsp)).
  - intros a _. exact (IH a mo (Hna a)).
Qed.

Section Lift.
Variable segs : list Segment.

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
Proof. intros c e st H. destruct H; cbn [cfg_model]; assumption. Qed.

Lemma msteps_cases : forall ms ms1, msteps segs ms ms1 ->
  ms1 = ms \/ exists ms2, mstep segs ms ms2 /\ msteps segs ms2 ms1.
Proof.
  intros ms ms1 H. destruct H as [ms0 | ms0 ms2 ms3 Hs Hr];
    [left; reflexivity | right; exists ms2; split; assumption].
Qed.

(** [ITreeCfg.tree_at] at the unfiltered node step. *)
Definition tat {R : Type} (t : itree node R) (Q : R -> machine_state -> Prop)
    (ms : machine_state) (mo : Model) : Prop :=
  impl segs (at_node segs) t Q ms /\ leaves_unreachable_m nstep t mo /\
  m_halted mo = None /\ minv mo /\ tsafe nstep nsafe t mo.

(** At a configuration a tree is at, a pending call is a node of the tree. *)
Lemma tree_na : forall R (t : itree node R) Q ms mo x8,
  tat t Q ms mo -> tna t ->
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros R t. induction t as [r|n k IH|v k IH]; intros Q ms mo x8 (Ht & Hl & Hh & Hinv & Hsf) Hna Hx.
  - exfalso. apply (Hl [] r mo). cbn [tpath]. split; [reflexivity | split; reflexivity].
  - cbn [impl] in Ht. destruct Ht as (ms1 & Hm & Hat & _).
    destruct (msteps_cases ms ms1 Hm) as [-> | (ms2 & Hs1 & _)].
    + destruct Hna as [Hn _]. exact (at_node_na n ms x8 Hat Hn Hx).
    + exfalso. destruct Hs1 as [Hn _]. congruence.
  - cbn [impl] in Ht. destruct Ht as (ms1 & Hm & a & Hv & Ha).
    destruct (msteps_cases ms ms1 Hm) as [-> | (ms2 & Hs1 & _)].
    + apply (IH a Q ms mo x8); [| exact (Hna a) | exact Hx].
      split; [exact Ha|]. split; [exact (leaves_unreachable_m_choice node nstep v k mo a Hl Hv)|].
      split; [exact Hh|]. split; [exact Hinv | exact (Hsf a Hv)].
    + exfalso. destruct Hs1 as [Hn _]. congruence.
Qed.

(** A step from a configuration a tree is at reaches a configuration that has
    halted or that a subtree is at ([ITree.impl_sstep_inv], unfiltered). *)
Lemma tat_step : forall R (t : itree node R) Q ms mo evs X,
  tat t Q ms mo -> tna t -> sstep segs (mkCfg ms mo) evs X ->
  exists c', X = SNext c' /\
    (m_halted (cfg_model c') <> None \/
     exists t' : itree node R, tat t' Q (cfg_ms c') (cfg_model c') /\ tna t').
Proof.
  intros R t. induction t as [r|n k IH|v k IH]; intros Q ms mo evs X HT Hna Hss;
    pose proof HT as (Ht & Hl & Hh & Hinv & Hsf);
    pose proof (ns_lazy _ _ _ _ _ _ _ (nodes_sound segs) mo Hinv) as Hlz.
  - exfalso. apply (Hl [] r mo). cbn [tpath]. split; [reflexivity | split; reflexivity].
  - cbn [impl] in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    destruct (msteps_cases ms ms1 Hm) as [-> | (ms2 & Hs1 & Hm2)].
    + destruct Hsf as [Hns Hks]. destruct Hna as [Hn Hkn].
      destruct (ns_complete _ _ _ _ _ _ _ (nodes_sound segs) n ms mo evs X Hat Hh Hinv Hns Hss)
        as [(rsp & mo' & -> & Hst) | (code & mo' & -> & Hex & _)].
      * destruct (ns_sound _ _ _ _ _ _ _ (nodes_sound segs) n ms mo rsp mo' evs Hat Hh Hinv Hns Hst)
          as (Hh' & Hinv' & _).
        exists (mkCfg (nret ms rsp) mo'). split; [reflexivity|]. right. exists (k rsp).
        cbn [cfg_ms cfg_model]. split; [|exact (Hkn rsp)].
        split; [exact (Hk rsp)|]. split.
        { intros tr r mo'' Hp. apply (Hl (evs ++ tr) r mo''). cbn [tpath].
          exists rsp, mo', evs, tr. split; [exact Hst | split; [exact Hp | reflexivity]]. }
        split; [exact Hh'|]. split; [exact Hinv'|]. exact (Hks rsp mo' evs Hst).
      * destruct (ns_exit _ _ _ _ _ _ _ (nodes_sound segs) n ms mo code mo' Hat Hh Hinv Hns Hex)
          as (Hh' & _).
        exists (mkCfg ms mo'). split; [reflexivity|]. left. cbn [cfg_model].
        rewrite Hh'. discriminate.
    + destruct (sstep_mstep_inv segs ms mo ms2 evs X Hlz Hs1 Hss) as [_ ->].
      exists (mkCfg ms2 mo). split; [reflexivity|]. right. exists (Vis n k).
      cbn [cfg_ms cfg_model]. split; [|exact Hna].
      split; [cbn [impl]; exists ms1; split; [exact Hm2 | split; [exact Hat | exact Hk]]|].
      split; [exact Hl|]. split; [exact Hh|]. split; [exact Hinv | exact Hsf].
  - cbn [impl] in Ht. destruct Ht as (ms1 & Hm & a & Hv & Ha).
    destruct (msteps_cases ms ms1 Hm) as [-> | (ms2 & Hs1 & Hm2)].
    + apply (IH a Q ms mo evs X); [| exact (Hna a) | exact Hss].
      split; [exact Ha|]. split; [exact (leaves_unreachable_m_choice node nstep v k mo a Hl Hv)|].
      split; [exact Hh|]. split; [exact Hinv | exact (Hsf a Hv)].
    + destruct (sstep_mstep_inv segs ms mo ms2 evs X Hlz Hs1 Hss) as [_ ->].
      exists (mkCfg ms2 mo). split; [reflexivity|]. right. exists (Choice v k).
      cbn [cfg_ms cfg_model]. split; [|exact Hna].
      split; [cbn [impl]; exists ms1; split; [exact Hm2 | exists a; split; [exact Hv | exact Ha]]|].
      split; [exact Hl|]. split; [exact Hh|]. split; [exact Hinv | exact Hsf].
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
    pose proof (ns_lazy _ _ _ _ _ _ _ (nodes_sound segs) mo Hinv) as Hlz.
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
