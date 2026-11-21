(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Lib/ITree.v's step inversion (impl_sstep_inv) and Lib/Cfg.v's acfg_nonspurious: a tree whose nodes make no allocation call proves the budget premise of every run it describes. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO pair). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg PropExec MState Mem Exec ITree Nodes RegsEquiv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import MSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

(** * A tree with no allocation node proves the budget premise

    The released plain proof of this harness states its walk as
    [ITree.impl] over a program tree: the machine reaches, by instruction
    steps, the system call that a node of the tree names, and goes on from
    each response.  [Top.Bridge.impl_realizes] turns that into a
    [Top.Realize.realizes] derivation, whose node condition [node_ok] is
    stated over [sstep_cfg segs ACFG]: the run that never refuses an
    allocation call spuriously.  A [realizes] derivation records nothing
    about which calls the run makes, so it cannot say that the budget never
    refuses one; this file reads the tree instead and needs no carrier.

    [budget_refused_at] (lps [Run.v]) is true at a running configuration
    in three cases: an instruction touches a lazy page the budget cannot
    back; the pending system call is a grant the budget refuses
    ([alloc_budget_refused_b]); or an outcome of the pending call touches
    such a page.  The first needs a lazy mapping, and [Nodes.minv] has
    none.  The second needs a call numbered 214, 216, 222 or 226
    ([Run.alloc_mark_sysnos]).  The third is the premise of an error step,
    which [node_sound]'s completeness half ([ns_complete]) excludes at a
    node of the tree.

    The invariant [Inv_na] holds at every configuration the run reaches
    under the unfiltered step [Run.sstep]: the process has halted, or the
    machine state is, up to [RegsEquiv.ms_eqv], at a tree [t]
    ([utree_ok]) with
    - [impl t Q]: the machine walks [t];
    - [twf t mo P] ([Spec.MSafe.twf]): every node of [t] is safe at the
      model it is reached with;
    - [m_halted mo = None] and [minv mo];
    - [tna t]: every node of [t] is writev, ioctl, set_tid_address or
      exit ([nna]), system calls 66, 29, 96 and 93 or 94.
    [Q] and [P] never hold together at a leaf ([QP]), so no leaf of the
    tree is ever reached: [impl] rules out the leaves [Q] rejects, [twf]
    the leaves [P] rejects.  An unfiltered step from such a configuration
    is an [ACFG] step ([sstep_acfg_na]): an instruction step has no
    refusal premise, and a call outside the allocation family is never a
    spurious refusal under [ACFG] ([Cfg.acfg_nonspurious]).  So
    [node_sound]'s completeness half applies to it, and
    [utree_never_refused] follows by [Run.never_budget_refused_ind]. *)

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

Lemma tna_ebind : forall A B (t : itree node (exc A)) (f : A -> itree node (exc B)),
  tna t -> (forall a, tna (f a)) -> tna (ebind t f).
Proof.
  intros A B t f. induction t as [r|n k IH]; intros Ht Hf.
  - destruct r as [|a]; [exact I | exact (Hf a)].
  - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. exact (IH rsp (Hk rsp) Hf).
Qed.

Local Ltac not_alloc_lit :=
  let Hin := fresh "Hin" in
  intros Hin; vm_compute in Hin;
  repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin] end;
  first [discriminate Hin | exact Hin].

(** At such a node, the pending call is not an allocation call. *)
Lemma at_node_na : forall segs n ms x8, at_node segs n ms -> nna n = true ->
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros segs n ms x8 Hat Hn Hx.
  destruct n; cbn [nna] in Hn; try discriminate Hn; cbn [at_node] in Hat;
  repeat match type of Hat with _ /\ _ => destruct Hat as [Hat _] end;
  lazymatch type of Hat with
  | _ \/ _ => destruct Hat as [Hat|Hat]; rewrite Hat in Hx; injection Hx as <-; not_alloc_lit
  | _ => rewrite Hat in Hx; injection Hx as <-; not_alloc_lit
  end.
Qed.

(** If a call is pending at [c], it is not an allocation call. *)
Definition no_alloc_pending (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.

(** Where no allocation call is pending, every step is an [ACFG] step.  LPS 727298f3: the three
    vDSO arms of [sstep] have their [sstep_cfg] twins with no filter premise, and the
    instruction's unmodeled arm reads that the pc is no vDSO entry. *)
Lemma sstep_acfg_na : forall segs c e st,
  no_alloc_pending c -> sstep segs c e st -> sstep_cfg segs ACFG c e st.
Proof.
  intros segs c e st Hg H. destruct H as
    [ms model ms' model' Hh Hs Hst
    | ms model Hh Hs Hst
    | ms model Hh Hs Hst Hnv
    | ms model fn n eff model' model'' evs Hh Hs Hacc Hfn Hno Hspec Hef Hh' Hmat
    | ms model fn n eff model' evs Hh Hs Hacc Hfn Hno Hspec Hef Hh' Hmat
    | ms model fn Hh Hs Hacc Hfn Hun
    | ms model x8 eff model' model'' evs Hh Hs Hspec Hh' Hmat
    | ms model x8 eff model' evs Hh Hs Hspec Hh' Hmat
    | ms model x8 eff model' evs code Hh Hs Hspec Hh' Hk
    | ms model x8 eff model' evs sig Hh Hs Hspec Hk
    | ms model x8 Hh Hs Hspec ].
  - exact (sstep_cfg_instr segs ACFG ms model ms' model' Hh Hs Hst).
  - exact (sstep_cfg_instr_fault segs ACFG ms model Hh Hs Hst).
  - exact (sstep_cfg_instr_unmodeled segs ACFG ms model Hh Hs Hst Hnv).
  - exact (sstep_cfg_vdso_call segs ACFG ms model fn n eff model' model'' evs Hh Hs Hacc Hfn Hno Hspec Hef Hh' Hmat).
  - exact (sstep_cfg_vdso_materialization_fault segs ACFG ms model fn n eff model' evs Hh Hs Hacc Hfn Hno Hspec Hef Hh' Hmat).
  - exact (sstep_cfg_vdso_unmodeled segs ACFG ms model fn Hh Hs Hacc Hfn Hun).
  - exact (sstep_cfg_syscall segs ACFG ms model x8 eff model' model'' evs Hh Hs Hspec
      (acfg_nonspurious (sys_input segs ms x8) model eff (Hg x8 Hs)) Hh' Hmat).
  - exact (sstep_cfg_syscall_materialization_fault segs ACFG ms model x8 eff model' evs Hh Hs Hspec
      (acfg_nonspurious (sys_input segs ms x8) model eff (Hg x8 Hs)) Hh' Hmat).
  - exact (sstep_cfg_exit segs ACFG ms model x8 eff model' evs code Hh Hs Hspec Hh' Hk).
  - exact (sstep_cfg_killed segs ACFG ms model x8 eff model' evs sig Hh Hs Hspec Hk).
  - exact (sstep_cfg_syscall_unmodeled segs ACFG ms model x8 Hh Hs Hspec).
Qed.

Lemma sstep_live : forall segs c e st, sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros segs c e st H. destruct H; cbn [cfg_model]; assumption. Qed.

Lemma msteps_cases : forall segs ms ms1, msteps segs ms ms1 ->
  ms1 = ms \/ exists ms2, mstep segs ms ms2 /\ msteps segs ms2 ms1.
Proof.
  intros segs ms ms1 H. destruct H as [ms0 | ms0 ms2 ms3 Hs Hr];
    [left; reflexivity | right; exists ms2; split; assumption].
Qed.

(** A tree the machine walks, safe at the model, with no allocation node. *)
Definition utree_ok (segs : list Segment) {R : Type} (Q : R -> machine_state -> Prop)
    (P : R -> Model -> Prop) (t : itree node R) (ms : machine_state) (mo : Model) : Prop :=
  impl segs (at_node segs) t Q ms /\ twf t mo P /\ m_halted mo = None /\ minv mo /\ tna t.

(** No leaf is reached: the machine is on its way to a node. *)
Lemma utree_ok_vis : forall segs R (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop),
  (forall r ms mo, Q r ms -> P r mo -> False) ->
  forall t ms mo, utree_ok segs Q P t ms mo ->
  exists n k ms1, t = Vis n k /\ msteps segs ms ms1 /\ at_node segs n ms1 /\
    (forall rsp, impl segs (at_node segs) (k rsp) Q (nret ms1 rsp)).
Proof.
  intros segs R Q P QP t ms mo (Ht & Hw & _ & _ & _).
  destruct t as [r|n k].
  - destruct Ht as (ms' & _ & HQ). exact (False_ind _ (QP r ms' mo HQ Hw)).
  - destruct Ht as (ms1 & Hm & Hat & Hk).
    exact (ex_intro _ n (ex_intro _ k (ex_intro _ ms1 (conj eq_refl (conj Hm (conj Hat Hk)))))).
Qed.

(** With a call pending, the machine is at the node. *)
Lemma utree_ok_pending : forall segs R (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop),
  (forall r ms mo, Q r ms -> P r mo -> False) ->
  forall t ms mo x8, utree_ok segs Q P t ms mo -> ms_svc_pending ms = Some x8 ->
  exists n k, t = Vis n k /\ at_node segs n ms /\
    (forall rsp, impl segs (at_node segs) (k rsp) Q (nret ms rsp)).
Proof.
  intros segs R Q P QP t ms mo x8 HT Hx.
  destruct (utree_ok_vis segs R Q P QP t ms mo HT) as (n & k & ms1 & Et & Hm & Hat & Hk).
  destruct (msteps_cases segs ms ms1 Hm) as [-> | (ms2 & Hs & _)].
  - exact (ex_intro _ n (ex_intro _ k (conj Et (conj Hat Hk)))).
  - exfalso. destruct Hs as [Hn _]. rewrite Hx in Hn. discriminate Hn.
Qed.

(** ...so a pending call is the node's, which is not an allocation call. *)
Lemma utree_ok_na : forall segs R (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop),
  (forall r ms mo, Q r ms -> P r mo -> False) ->
  forall t ms mo x8, utree_ok segs Q P t ms mo -> ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros segs R Q P QP t ms mo x8 HT Hx.
  destruct (utree_ok_pending segs R Q P QP t ms mo x8 HT Hx) as (n & k & Et & Hat & _).
  destruct HT as (_ & _ & _ & _ & Hna). subst t. destruct Hna as [Hn _].
  exact (at_node_na segs n ms x8 Hat Hn Hx).
Qed.

(** The invariant of every configuration the unfiltered run reaches. *)
Definition Inv_na (segs : list Segment) {R : Type} (Q : R -> machine_state -> Prop)
    (P : R -> Model -> Prop) (c : config) : Prop :=
  m_halted (cfg_model c) <> None \/
  exists (t : itree node R) ms0, ms_eqv (cfg_ms c) ms0 /\ utree_ok segs Q P t ms0 (cfg_model c).

Lemma Inv_na_step : forall segs R (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop),
  (forall r ms mo, Q r ms -> P r mo -> False) ->
  forall c evs c', Inv_na segs Q P c -> sstep segs c evs (SNext c') -> Inv_na segs Q P c'.
Proof.
  intros segs R Q P QP [ms mo] evs c' HI Hss.
  destruct HI as [Hh | (t & ms0 & Heqv & HT)]; cbn [cfg_ms cfg_model] in *.
  - exfalso. apply Hh. exact (sstep_live segs _ _ _ Hss).
  - destruct (sstep_eqv segs ms ms0 mo evs (SNext c') Heqv Hss) as (X' & Hss0 & HX).
    pose proof HT as (Ht & Hw & Hh & Hinv & Hna).
    destruct (utree_ok_vis segs R Q P QP t ms0 mo HT) as (n & k & ms1 & Et & Hm & Hat & Hk).
    destruct (msteps_cases segs ms0 ms1 Hm) as [-> | (ms2 & Hs1 & Hr)].
    + (* The machine is at the node: the step is the node's. *)
      assert (Hg : no_alloc_pending (mkCfg ms0 mo)).
      { intros x8 Hx. exact (utree_ok_na segs R Q P QP t ms0 mo x8 HT Hx). }
      pose proof (sstep_acfg_na segs _ evs X' Hg Hss0) as Hcfg.
      subst t. destruct Hw as [Hsafe Hwk]. destruct Hna as [_ Hnak].
      destruct (ns_complete _ _ _ _ _ _ _ _ (nodes_sound segs) n ms0 mo evs X' Hat Hh Hinv Hsafe Hcfg)
        as [(rsp & mo' & EX & Hst) | (code & mo' & EX & Hex & _)]; subst X'.
      * destruct (ns_sound _ _ _ _ _ _ _ _ (nodes_sound segs) n ms0 mo rsp mo' evs Hat Hh Hinv Hsafe Hst)
          as (Hh' & Hinv' & _).
        destruct c' as [ms' mo'']. destruct HX as [He Hmo]. cbn [cfg_ms cfg_model] in He, Hmo. subst mo''.
        right. exists (k rsp), (nret ms0 rsp). split; [exact He|].
        exact (conj (Hk rsp) (conj (Hwk rsp mo' evs Hst) (conj Hh' (conj Hinv' (Hnak rsp))))).
      * destruct (ns_exit _ _ _ _ _ _ _ _ (nodes_sound segs) n ms0 mo code mo' Hat Hh Hinv Hsafe Hex)
          as [Hh' _].
        destruct c' as [ms' mo'']. destruct HX as [_ Hmo]. cbn [cfg_ms cfg_model] in Hmo. subst mo''.
        left. cbn [cfg_model]. rewrite Hh'. discriminate.
    + (* An instruction step on the way to the node. *)
      assert (Hg : no_alloc_pending (mkCfg ms0 mo)).
      { intros x8 Hx. destruct Hs1 as [Hn _]. cbn [cfg_ms] in Hx. rewrite Hx in Hn. discriminate Hn. }
      pose proof (sstep_acfg_na segs _ evs X' Hg Hss0) as Hcfg.
      destruct (sstep_mstep_inv segs ACFG ms0 mo ms2 evs X' (minv_nolazy mo Hinv) Hs1 Hcfg) as [_ EX].
      subst X'.
      destruct c' as [ms' mo'']. destruct HX as [He Hmo]. cbn [cfg_ms cfg_model] in He, Hmo. subst mo''.
      right. exists t, ms2. split; [exact He|].
      refine (conj _ (conj Hw (conj Hh (conj Hinv Hna)))).
      subst t. cbn [impl]. unfold evt. exists ms1. exact (conj Hr (conj Hat Hk)).
Qed.

Lemma Inv_na_not_refused : forall segs R (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop),
  (forall r ms mo, Q r ms -> P r mo -> False) ->
  forall c, Inv_na segs Q P c -> ~ budget_refused_at segs c.
Proof.
  intros segs R Q P QP [ms mo] HI Hb.
  destruct HI as [Hh | (t & ms0 & Heqv & HT)]; cbn [cfg_ms cfg_model] in *.
  - apply Hh. exact (proj1 Hb).
  - pose proof HT as (_ & _ & Hh & Hinv & _).
    pose proof (minv_nolazy mo Hinv) as Hlz.
    pose proof Heqv as (_ & _ & _ & Hsvc & _).
    pose proof Hb as Hb0.
    destruct Hb as (_ & [(Hnone & _) | (x8 & Hx & [Hgr | (eff & mo' & e & Hsp & Hh' & Hm)])]);
      cbn [cfg_ms cfg_model] in *.
    + exact (budget_refused_at_no_lazy_instr segs ms mo Hlz Hnone Hb0).
    + assert (Hx0 : ms_svc_pending ms0 = Some x8) by (rewrite <- Hsvc; exact Hx).
      pose proof (alloc_budget_refused_b_outside (sys_input segs ms x8) mo
                    (utree_ok_na segs R Q P QP t ms0 mo x8 HT Hx0)) as Hf.
      change (alloc_budget_refused_b (sys_input segs ms x8) mo = true) in Hgr. congruence.
    + assert (Hx0 : ms_svc_pending ms0 = Some x8) by (rewrite <- Hsvc; exact Hx).
      rewrite (sys_input_eqv segs ms ms0 x8 Heqv) in Hsp.
      pose proof (budget_fault_syscall_sstep_error segs ms0 mo x8 eff mo' e Hh Hx0 Hsp Hh' Hm) as Herr.
      assert (Hg : no_alloc_pending (mkCfg ms0 mo)).
      { intros y Hy. exact (utree_ok_na segs R Q P QP t ms0 mo y HT Hy). }
      pose proof (sstep_acfg_na segs _ [] SError Hg Herr) as Hcfg.
      destruct (utree_ok_pending segs R Q P QP t ms0 mo x8 HT Hx0) as (n & k & Et & Hat & _).
      destruct HT as (_ & Hw & _ & _ & _). subst t. destruct Hw as [Hsafe _].
      destruct (ns_complete _ _ _ _ _ _ _ _ (nodes_sound segs) n ms0 mo [] SError Hat Hh Hinv Hsafe Hcfg)
        as [(? & ? & E & _) | (? & ? & E & _)]; discriminate E.
Qed.

(** A run that starts, up to [ms_eqv], where a tree with no allocation node
    is, never reaches a budget-refused configuration (unfiltered step). *)
Theorem utree_never_refused : forall segs R (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop),
  (forall r ms mo, Q r ms -> P r mo -> False) ->
  forall t ms0 ms mo, ms_eqv ms ms0 -> utree_ok segs Q P t ms0 mo ->
  ~ reaches_budget_refused segs (mkCfg ms mo).
Proof.
  intros segs R Q P QP t ms0 ms mo Heqv HT.
  apply (never_budget_refused_ind segs (Inv_na segs Q P)).
  - right. exists t, ms0. exact (conj Heqv HT).
  - intros c e c' HI Hs. exact (Inv_na_step segs R Q P QP c e c' HI Hs).
  - intros c HI. exact (Inv_na_not_refused segs R Q P QP c HI).
Qed.
