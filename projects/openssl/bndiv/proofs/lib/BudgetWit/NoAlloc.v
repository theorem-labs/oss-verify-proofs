(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Lib/ITree.v's run invariant (run_inv): a tree whose nodes make no allocation call proves the budget premise of every run it describes. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: sstep_ncfg covers sstep's three vDSO arms, which sstep_cfg mirrors with no filter premise, and the vDSO-entry premise of the unmodeled-instruction arm. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes RegsEquiv LimBase.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(** * A tree with no allocation node proves the budget premise

    The released proofs of this harness state each walk as [ITree.impl]: the
    machine reaches, by instruction steps, the system call that a node of a
    program tree names, and goes on from each response.  [ITree.tree_at] adds
    that no leaf of the tree is reached and that each node is safe, and
    [ITree.run_inv] is the invariant of every configuration the run reaches
    under [Cfg.ncfg]: a tree is at it, or the process has halted.  No
    [realizes] derivation is built on this path, so there is no carrier to
    add a grant check to.

    [budget_refused_at] (lps [Run.v]) is true at a running configuration in
    three cases: an instruction touches a lazy page the budget cannot back;
    the pending system call is a grant the budget refuses
    ([alloc_budget_refused_b]); or an outcome of the pending call touches such
    a page.  The first needs a lazy mapping, and [Nodes.minv] has none.  The
    second needs a call numbered 214, 216, 222 or 226
    ([Run.alloc_mark_sysnos]).  The third is the premise of an error step,
    which [ITree.impl_sstep_inv] excludes at a tree's node.

    So the invariant here is [ITree.run_inv] with one more clause: every node
    of the tree at the configuration is one of [NWritev], [NIoctl],
    [NSetTid], [NExit] ([nna], [tna]); these are system calls 66, 29, 96 and
    93 or 94.  [tree_never_refused] reads it over the unfiltered step
    [Run.sstep], so no configuration the run reaches is budget-refused under
    any spurious-failure configuration.  The step is moved to [Cfg.ncfg],
    where the tree's facts hold, because on a call outside the allocation
    family [ncfg] filters nothing ([sstep_ncfg]).  The invariant also carries
    a register equivalence ([RegsEquiv.ms_eqv]), because the released trees
    start at [RegsEquiv.init_ms] and the run at [Run.init_machine_state].

    The four nodes leave the limit untouched, so their tree's leaves are
    unreachable at any limit when they are at one ([leaves_setL]), and their
    safety condition is [True] ([tsafe_na]). *)

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

(** The family [ncfg] reads as forced-only is the allocation family, whose
    numbers are [alloc_mark_sysnos] ([Run.alloc_family_dispatched]). *)
Lemma family_on_ncfg : forall i,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off ncfg i = false.
Proof.
  intros i Hn. unfold injected_family_off.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [a|] eqn:E; [|reflexivity].
  destruct (ia_family a) eqn:F; try reflexivity.
  exfalso. exact (Hn (alloc_family_dispatched _ a E F)).
Qed.

Local Ltac not_alloc_lit :=
  let Hin := fresh "Hin" in
  intros Hin; vm_compute in Hin;
  repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin] end;
  first [discriminate Hin | exact Hin].

(** The four setL lemmas: the four nodes do not read or change the limit. *)
Lemma nstep_setL : forall n mo rsp mo' evs L, nna n = true ->
  nstep n mo rsp mo' evs -> nstep n (setL L mo) rsp (setL L mo') evs.
Proof.
  intros n mo rsp mo' evs L Hn H.
  destruct n; cbn [nna] in Hn; try discriminate Hn; cbn [nstep] in *.
  - destruct H as [-> H]. split; [reflexivity | exact H].
  - destruct H as (He & Hf & ->). split; [exact He | split; [exact Hf | reflexivity]].
  - destruct H as (He & t & Hf & H). split; [exact He|]. exists t. split; [exact Hf|].
    change (m_tid (setL L mo)) with (m_tid mo).
    revert H. destruct (m_tid mo) as [t0|]; intros H; destruct H as [Ht ->]; (split; [exact Ht | reflexivity]).
  - exact H.
Qed.

Lemma tpath_setL : forall R (t : itree node R) mo tr r mo' L, tna t ->
  tpath nstep t mo tr r mo' -> tpath nstep t (setL L mo) tr r (setL L mo').
Proof.
  intros R t. induction t as [r0|n k IH]; intros mo tr r mo' L Hna Hp; cbn [tpath] in *.
  - destruct Hp as (-> & -> & ->). split; [reflexivity | split; reflexivity].
  - destruct Hna as [Hn Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & ->).
    exists rsp, (setL L mo1), evs, tr'.
    split; [exact (nstep_setL n mo rsp mo1 evs L Hn Hst)|].
    split; [exact (IH rsp mo1 tr' r mo' L (Hk rsp) Hp) | reflexivity].
Qed.

(** A path of the tree at [mo] is a path at [setL L mo], so the leaves are
    unreachable at [mo] when they are at [setL L mo]. *)
Lemma leaves_setL : forall R (t : itree node R) mo L, tna t ->
  leaves_unreachable_m nstep t (setL L mo) -> leaves_unreachable_m nstep t mo.
Proof.
  intros R t mo L Hna Hl tr r mo' Hp.
  exact (Hl tr r (setL L mo') (tpath_setL R t mo tr r mo' L Hna Hp)).
Qed.

Lemma tsafe_na : forall R (t : itree node R) mo, tna t -> tsafe nstep nsafe t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo Hna; cbn [tsafe]; [exact I|].
  destruct Hna as [Hn Hk]. split.
  - destruct n; cbn [nna] in Hn; try discriminate Hn; exact I.
  - intros rsp mo' evs _. exact (IH rsp mo' (Hk rsp)).
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

(** On a call outside the allocation family, [ncfg] filters no step. *)
Lemma sstep_ncfg : forall c evs X,
  (forall x8, ms_svc_pending (cfg_ms c) = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos) ->
  sstep segs c evs X -> sstep_cfg segs ncfg c evs X.
Proof.
  intros c evs X Hna H. revert Hna.
  (* LPS 727298f3: [sstep] has eleven constructors; the three vDSO arms (slots 4-6)
     have no pending call, and [sstep_cfg] mirrors them with no filter premise;
     [instr_unmodeled] now also says the pc is no vDSO entry ([Hv]). *)
  destruct H as [ ms mo ms' mo' Hh Hs Ha | ms mo Hh Hs Ha | ms mo Hh Hs Ha Hv
                | ms mo fn n eff mo' mo'' e Hh Hs Ha Hf Hn Hsp Hef Hh' Hm
                | ms mo fn n eff mo' e Hh Hs Ha Hf Hn Hsp Hef Hh' Hm
                | ms mo fn Hh Hs Ha Hf Hu
                | ms mo x8 eff mo' mo'' e Hh Hs Hsp Hh' Hm
                | ms mo x8 eff mo' e Hh Hs Hsp Hh' Hm
                | ms mo x8 eff mo' e code Hh Hs Hsp Hh' Hk
                | ms mo x8 eff mo' e sg Hh Hs Hsp Hk
                | ms mo x8 Hh Hs Hsp ];
    intros Hna; cbn [cfg_ms] in Hna.
  - exact (sstep_cfg_instr segs ncfg ms mo ms' mo' Hh Hs Ha).
  - exact (sstep_cfg_instr_fault segs ncfg ms mo Hh Hs Ha).
  - exact (sstep_cfg_instr_unmodeled segs ncfg ms mo Hh Hs Ha Hv).
  - exact (sstep_cfg_vdso_call segs ncfg ms mo fn n eff mo' mo'' e Hh Hs Ha Hf Hn Hsp Hef Hh' Hm).
  - exact (sstep_cfg_vdso_materialization_fault segs ncfg ms mo fn n eff mo' e Hh Hs Ha Hf Hn Hsp Hef Hh' Hm).
  - exact (sstep_cfg_vdso_unmodeled segs ncfg ms mo fn Hh Hs Ha Hf Hu).
  - refine (sstep_cfg_syscall segs ncfg ms mo x8 eff mo' mo'' e Hh Hs Hsp _ Hh' Hm).
    apply spurious_refusal_family_on, family_on_ncfg. exact (Hna x8 Hs).
  - refine (sstep_cfg_syscall_materialization_fault segs ncfg ms mo x8 eff mo' e Hh Hs Hsp _ Hh' Hm).
    apply spurious_refusal_family_on, family_on_ncfg. exact (Hna x8 Hs).
  - exact (sstep_cfg_exit segs ncfg ms mo x8 eff mo' e code Hh Hs Hsp Hh' Hk).
  - exact (sstep_cfg_killed segs ncfg ms mo x8 eff mo' e sg Hh Hs Hsp Hk).
  - exact (sstep_cfg_syscall_unmodeled segs ncfg ms mo x8 Hh Hs Hsp).
Qed.

Lemma msteps_cases : forall ms ms1, msteps segs ms ms1 ->
  ms1 = ms \/ exists ms2, mstep segs ms ms2 /\ msteps segs ms2 ms1.
Proof.
  intros ms ms1 H. destruct H as [ms0 | ms0 ms2 ms3 Hs Hr];
    [left; reflexivity | right; exists ms2; split; assumption].
Qed.

(** At a configuration a tree is at, a pending call is the tree's first node. *)
Lemma tree_na : forall R (t : itree node R) Q ms mo x8,
  tree_at segs (at_node segs) nstep minv nsafe t Q ms mo -> tna t ->
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

(** [ITree.run_inv], with the tree's nodes outside the allocation family and
    the machine state up to [RegsEquiv.ms_eqv]. *)
Definition Inv_na {R : Type} (Q : R -> machine_state -> Prop) (c : config) : Prop :=
  m_halted (cfg_model c) <> None \/
  exists (t : itree node R) ms0, ms_eqv (cfg_ms c) ms0 /\
    tree_at segs (at_node segs) nstep minv nsafe t Q ms0 (cfg_model c) /\ tna t.

Lemma Inv_na_step : forall R Q c evs c', Inv_na (R:=R) Q c -> sstep segs c evs (SNext c') -> Inv_na Q c'.
Proof.
  intros R Q [ms mo] evs c' HI Hss.
  destruct HI as [Hh | (t & ms0 & Heqv & HT & Hna)]; cbn [cfg_ms cfg_model] in *.
  - exfalso. apply Hh. exact (sstep_live _ _ _ Hss).
  - destruct (sstep_eqv segs ms ms0 mo evs (SNext c') Heqv Hss) as (X' & Hss0 & HX).
    assert (Hcfg : sstep_cfg segs ncfg (mkCfg ms0 mo) evs X').
    { apply sstep_ncfg; [|exact Hss0]. intros x8 Hx. exact (tree_na R t Q ms0 mo x8 HT Hna Hx). }
    destruct (impl_sstep_inv node segs ncfg (at_node segs) nstep nexit minv nsafe (nodes_sound segs)
                t Q ms0 mo evs X' HT Hcfg)
      as [(ms1 & -> & _ & _ & HT1) | [(n & k & rsp & mo1 & Et & _ & -> & _ & HT1) | (n & k & code & mo1 & _ & _ & -> & _ & _ & Hh1)]];
      destruct HX as [He Hm]; cbn [cfg_ms cfg_model] in He, Hm.
    + right. exists t, ms1. rewrite Hm. split; [exact He|]. split; [exact HT1 | exact Hna].
    + right. exists (k rsp), (nret ms0 rsp). rewrite Hm. split; [exact He|]. split; [exact HT1|].
      subst t. destruct Hna as [_ Hk]. exact (Hk rsp).
    + left. rewrite Hm. rewrite Hh1. discriminate.
Qed.

Lemma Inv_na_not_refused : forall R Q c, Inv_na (R:=R) Q c -> ~ budget_refused_at segs c.
Proof.
  intros R Q [ms mo] HI Hb.
  destruct HI as [Hh | (t & ms0 & Heqv & HT & Hna)]; cbn [cfg_ms cfg_model] in *.
  - apply Hh. exact (proj1 Hb).
  - pose proof HT as (_ & _ & Hh & Hinv & _).
    pose proof (ns_lazy _ _ _ _ _ _ _ _ (nodes_sound segs) mo Hinv) as Hlz.
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
      assert (Hcfg : sstep_cfg segs ncfg (mkCfg ms0 mo) [] SError).
      { apply sstep_ncfg; [|exact Herr]. intros y Hy. exact (tree_na R t Q ms0 mo y HT Hna Hy). }
      destruct (impl_sstep_inv node segs ncfg (at_node segs) nstep nexit minv nsafe (nodes_sound segs)
                  t Q ms0 mo [] SError HT Hcfg)
        as [(? & E & _) | [(? & ? & ? & ? & _ & _ & E & _) | (? & ? & ? & ? & _ & _ & E & _)]];
        discriminate E.
Qed.

(** A run that starts, up to [ms_eqv], where a tree with no allocation node
    is, never reaches a budget-refused configuration (unfiltered step). *)
Theorem tree_never_refused : forall R (t : itree node R) Q ms0 ms mo,
  ms_eqv ms ms0 -> tree_at segs (at_node segs) nstep minv nsafe t Q ms0 mo -> tna t ->
  ~ reaches_budget_refused segs (mkCfg ms mo).
Proof.
  intros R t Q ms0 ms mo Heqv HT Hna.
  apply (never_budget_refused_ind segs (Inv_na (R:=R) Q)).
  - right. exists t, ms0. split; [exact Heqv | split; [exact HT | exact Hna]].
  - intros c e c' HI Hs. exact (Inv_na_step R Q c e c' HI Hs).
  - intros c HI. exact (Inv_na_not_refused R Q c HI).
Qed.

End Lift.
