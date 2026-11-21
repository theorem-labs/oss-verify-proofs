(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Top/ImplRzCfg.v and Spec/MSil.v: the tree predicate tfree (no allocation node), and impl_trz_realizes_leaf_cfg restated over BudgetWit.RzbCfg.rzb_cfg for trees with no allocation node. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the five-entry alloc_mark_sysnos with munmap 215, and each rzb_cfg node's sys_rob premise from nsc_rob). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree ITreeCfg Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Monad.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BudgetWit Require Import RzbCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(** * Trees with no allocation node, and the bridge from [impl] to [rzb_cfg]

    The tree's walks reach syscalls through [Top.ImplRzCfg.impl_trz_realizes_leaf_cfg]:
    a machine-level [impl] proof of an interaction tree, and a [trz] derivation
    of its trace set, give [realizes_cfg] at the tree's start.  At each [Vis]
    node the bridge builds a [realizes_cfg] node at the configuration where the
    syscall is pending.  [impl_trz_rzb_leaf] is that bridge over
    [BudgetWit.RzbCfg.rzb_cfg]: it asks besides that the tree has no allocation
    node ([tfree]: [NodesCfg.alloc_node] is [false] at each node), which gives
    the two node checks of [rzb_cfg]: the grant check because only an allocation
    syscall (214, 216, 222, 226) carries a budget mark
    ([Run.alloc_budget_refused_b_outside]), the unfiltered-step check because
    the filter removes an outcome only at a node [NodesCfg.node_off] marks
    ([NodesCfg.node_off_link], [Run.spurious_refusal_family_on]), which for
    [alloc_only_cfg false] is an allocation node ([NodesCfg.node_off_acfg]).

    [tfree_bind] and the [M]-combinator lemmas follow [Spec.MSil]'s [tmm]
    lemmas. *)

Fixpoint tfree {R : Type} (t : itree node R) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => alloc_node n = false /\ forall rsp, tfree (k rsp)
  end.

Lemma tfree_bind : forall {A B} (t : itree node A) (f : A -> itree node B),
  tfree t -> (forall a, tfree (f a)) -> tfree (ITree.bind node t f).
Proof.
  intros A B t; induction t as [r | n k IH]; intros f Ht Hf; cbn in *; [apply Hf|].
  destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. apply IH; [apply Hk| exact Hf].
Qed.

Section TF.
Context {St : Type}.
Local Notation MS := (Monad.M St).

Lemma tfree_mret : forall {A} (a : A) (s : St), tfree (mret a s).
Proof. intros. exact I. Qed.
Lemma tfree_munr : forall {A} (s : St), tfree (munr (A:=A) s).
Proof. intros. exact I. Qed.
Lemma tfree_mget : forall (s : St), tfree (mget s).
Proof. intros. exact I. Qed.
Lemma tfree_mupd : forall f (s : St), tfree (mupd f s).
Proof. intros. exact I. Qed.
Lemma tfree_mbind : forall {A B} (m : MS A) (f : A -> MS B) (s : St),
  tfree (m s) -> (forall a s', tfree (f a s')) -> tfree (mbind m f s).
Proof.
  intros A B m f s Hm Hf. unfold mbind, ebind. apply tfree_bind; [exact Hm|]. intros [|[a s']]; [exact I| apply Hf].
Qed.
Lemma tfree_msys : forall {A} n (dec : resp -> option A) (s : St), alloc_node n = false -> tfree (msys n dec s).
Proof. intros A n dec s Hn. unfold msys, enode. cbn. split; [exact Hn|]. intros rsp. destruct (dec rsp); exact I. Qed.
End TF.

Section Bridge.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
(** The filter removes outcomes only at allocation nodes. *)
Hypothesis OFF : forall n, alloc_node n = false -> node_off cfg n = false.

Local Notation NS := (nodes_sound_cfg cfg segs).
Local Notation implN := (impl segs (at_node segs)).
Local Notation trzN := (trz node (nstep_cfg cfg) nexit minv nsafe).
Local Notation ans_idxN := (ans_idx node (nstep_cfg cfg) nexit).
Local Notation ans_evsN := (ans_evs node (nstep_cfg cfg) nexit).
Local Notation nxcfgN := (nxcfg node (nstep_cfg cfg) nexit).

(** At a configuration where a node that is not an allocation node is pending,
    the two node checks of [rzb_cfg] hold. *)
Lemma node_checks : forall n ms mo,
  at_node segs n ms -> alloc_node n = false ->
  grant_ok segs (mkCfg ms mo) /\ unfiltered cfg segs (mkCfg ms mo).
Proof.
  intros n ms mo Hat Hn. split.
  - intros x8 Hx8. cbn [cfg_ms cfg_model] in Hx8 |- *.
    destruct (at_node_svc segs n ms Hat) as (x8' & Hsvc' & K & -> & Harm & HK & _).
    assert (x8 = Z_to_bv 64 K) by congruence. subst x8.
    apply alloc_budget_refused_b_outside.
    change (in_sysno (sys_input segs ms (Z_to_bv 64 K))) with (Z_to_bv 64 K). rewrite HK.
    unfold alloc_mark_sysnos. cbn [In].
    (* LPS 727298f3: [alloc_mark_sysnos] is [214; 215; 216; 222; 226] (munmap 215 added). *)
    intros Hin. destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
      destruct n; cbn [alloc_node] in Hn; try discriminate Hn; vm_compute in Harm; congruence.
  - intros e st Hs. destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
    + apply (sstep_cfg_of_sstep cfg segs ms mo e st Hs).
      intros x8' eff m' evs' Hx8' _ _. rewrite Hsvc in Hx8'. injection Hx8' as <-.
      apply spurious_refusal_family_on.
      rewrite (node_off_link segs cfg n ms x8 Hat Hsvc). apply OFF. exact Hn.
    + exact (sstep_cfg_of_sstep_instr cfg segs ms mo e st Hsvc Hs).
Qed.

(** [ImplRzCfg.impl_trz_realizes_leaf_cfg] over [rzb_cfg], for a tree with no
    allocation node. *)
Theorem impl_trz_rzb_leaf : forall {R} (t : itree node R) Q ms mo (K : R -> Model -> TSet) T,
  implN t Q ms ->
  trzN t mo K T ->
  tfree t ->
  m_halted mo = None -> minv mo ->
  (forall r ms' mo', Q r ms' -> ImplRzCfg.leaf (nstep_cfg cfg) t mo r mo' -> m_halted mo' = None -> minv mo' ->
     rzb_cfg cfg segs (mkCfg ms' mo') (K r mo')) ->
  rzb_cfg cfg segs (mkCfg ms mo) T.
Proof.
  intros R t Q ms mo K T Himpl Htrz. revert ms Himpl.
  induction Htrz as [r mo K | n k mo K TT i0 Hminv Hsafe Hk IH Hex | t mo K T T' Ht IH Heq];
    intros ms Himpl Hfree Hh Hmi HK.
  - cbn in Himpl. destruct Himpl as (ms' & Hms & HQ).
    eapply rzb_msteps_lib_cfg; [exact Hh | apply (nsc_lazy _ _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    apply HK; [exact HQ | constructor | exact Hh | exact Hmi].
  - cbn in Himpl. destruct Himpl as (ms1 & Hms & Hat & Hcont).
    cbn [tfree] in Hfree. destruct Hfree as [Hn Hfk].
    eapply rzb_msteps_lib_cfg; [exact Hh | apply (nsc_lazy _ _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    destruct (node_checks n ms1 mo Hat Hn) as [Hg Hu].
    apply (rzb_node_cfg cfg segs (mkCfg ms1 mo) (ans_idxN n mo) (ans_evsN n mo) (nxcfgN n mo ms1) TT i0).
    + apply (node_ok_at_cfg cfg node segs (at_node segs) (nstep_cfg cfg) nexit minv nsafe NS); assumption.
    + exact Hg.
    + exact Hu.
    + exact (nsc_rob _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hmi).
    + intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn.
      * destruct (nsc_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hmi Hsafe Hst) as (Hh' & Hmi' & _).
        apply (IH rsp mo' evs Hst (nret ms1 rsp) (Hcont rsp) (Hfk rsp) Hh' Hmi').
        intros r ms' mo'' HQ HL Hh'' Hmi''. apply HK; [exact HQ | | exact Hh'' | exact Hmi''].
        eapply ImplRzCfg.leaf_vis; [exact Hst | exact HL].
      * rewrite (Hex code mo' Hxt).
        apply rzb_halt_cfg. cbn.
        destruct (nsc_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hmi Hsafe Hxt) as (Hh' & _).
        rewrite Hh'. discriminate.
  - eapply rzb_conseq_cfg; [apply IH; assumption | exact Heq].
Qed.
End Bridge.

(** [alloc_only_cfg false] filters only allocation nodes. *)
Lemma acfg_off : forall n, alloc_node n = false -> node_off acfg n = false.
Proof. intros n Hn. rewrite node_off_acfg. exact Hn. Qed.
