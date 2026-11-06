(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree ITreeCfg Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg TrzNodesCfg TrzStdioCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition LU {R : Type} (t : itree node R) (mo : Model) (K : R -> Model -> TSet) : TSet :=
  fun tr => tr = [] \/ exists r mo', leaf t mo r mo' /\ K r mo' tr.

Lemma LU_ret : forall {R} (r : R) mo K, K r mo [] -> t_eq (K r mo) (LU (Ret r) mo K).
Proof.
  intros R r mo K Hn tr. unfold LU. split.
  - intros H. right. exists r, mo. split; [constructor | exact H].
  - intros [-> | (r' & mo' & L & H)]; [exact Hn|]. apply leaf_ret_inv in L as [-> ->]. exact H.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tsil_leaf : forall {R} (t : itree node R) mo (P : R -> Model -> Prop) r mo',
  ImplRz.tsil node (nstep_cfg acfg) nexit nsafe t mo P -> leaf t mo r mo' -> P r mo'.
Proof.
  intros R t; induction t as [r0 | n k IH]; intros mo P r mo' Hs L.
  - apply leaf_ret_inv in L as [-> ->]. exact Hs.
  - inversion L; subst. cbn in Hs. destruct Hs as (_ & _ & Hk).
    match goal with Hst : (nstep_cfg acfg) _ _ ?rsp ?mo1 ?evs, Hl : leaf _ _ _ _ |- _ =>
      exact (IH rsp mo1 P r mo' (proj2 (Hk _ _ _ Hst)) Hl) end.
Qed.

Lemma mok_leaf : forall {R} (t : itree node R) mo (P : R -> Model -> Prop) r mo',
  ImplRz.tsil node (nstep_cfg acfg) nexit nsafe t mo P -> mok mo -> leaf t mo r mo' -> mok mo'.
Proof.
  intros R t; induction t as [r0 | n k IH]; intros mo P r mo' Hs Hok L.
  - apply leaf_ret_inv in L as [-> ->]. exact Hok.
  - inversion L; subst. cbn in Hs. destruct Hs as (Hsafe & _ & Hk).
    match goal with Hst : (nstep_cfg acfg) _ _ ?rsp ?mo1 ?evs, Hl : leaf _ _ _ _ |- _ =>
      exact (IH rsp mo1 P r mo' (proj2 (Hk _ _ _ Hst)) (mok_step _ _ _ _ _ Hok Hsafe Hst) Hl) end.
Qed.

Section ImplSplit.
Variable segs : list Segment.
Let NS := nodes_sound_cfg acfg segs.

Theorem impl_tsil_realizes_LU : forall {R} (t : itree node R) Q ms mo P (K : R -> Model -> TSet),
  impl segs (at_node segs) t Q ms ->
  ImplRz.tsil node (nstep_cfg acfg) nexit nsafe t mo P ->
  m_halted mo = None -> minv mo ->
  (forall r ms' mo', Q r ms' -> P r mo' -> leaf t mo r mo' -> m_halted mo' = None -> minv mo' ->
     realizes_cfg acfg segs (mkCfg ms' mo') (K r mo')) ->
  realizes_cfg acfg segs (mkCfg ms mo) (LU t mo K).
Proof.
  intros R t; induction t as [r | n k IH]; intros Q ms mo P K Himpl Hsil Hh Hmi HK; cbn in Himpl, Hsil.
  - destruct Himpl as (ms' & Hms & HQ).
    eapply rz_msteps_lib_cfg; [exact Hh | apply (nsc_lazy _ _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    assert (HR : realizes_cfg acfg segs (mkCfg ms' mo) (K r mo)).
    { apply (HK r ms' mo HQ Hsil); [constructor | exact Hh | exact Hmi]. }
    eapply rz_conseq_cfg; [exact HR | apply LU_ret]. exact (realizes_cfg_nonempty acfg segs _ _ HR).
  - destruct Himpl as (ms1 & Hms & Hat & Hcont).
    destruct Hsil as (Hsafe & Hnx & Hk).
    assert (Hex : exists rsp0 mo0 evs0, (nstep_cfg acfg) n mo rsp0 mo0 evs0).
    { destruct (nsc_progress _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hmi Hsafe)
        as [(rsp0 & mo0 & evs0 & H0) | (code & mo' & H)]; [exists rsp0, mo0, evs0; exact H0|].
      exfalso. exact (Hnx code mo' H). }
    destruct Hex as (rsp0 & mo0 & evs0 & H0).
    eapply rz_msteps_lib_cfg; [exact Hh | apply (nsc_lazy _ _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    eapply rz_conseq_cfg.
    + apply (rz_node_cfg acfg segs (mkCfg ms1 mo) (ans_idx node (nstep_cfg acfg) nexit n mo) (ans_evs node (nstep_cfg acfg) nexit n mo)
               (nxcfg node (nstep_cfg acfg) nexit n mo ms1)
               (fun i => match i with
                         | inl (exist _ p _) => LU (k (fst (fst p))) (snd (fst p)) K
                         | inr _ => t_nil
                         end)
               (inl (exist _ (rsp0, mo0, evs0) H0))).
      * apply (node_ok_at_cfg acfg node segs (at_node segs) (nstep_cfg acfg) nexit minv nsafe NS); assumption.
      * intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn.
        -- destruct (nsc_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hmi Hsafe Hst) as (Hh' & Hmi' & _).
           destruct (Hk rsp mo' evs Hst) as [_ Hsil'].
           apply (IH rsp Q (nret ms1 rsp) mo' P K (Hcont rsp) Hsil' Hh' Hmi').
           intros r ms' mo'' HQ HP L. apply HK; [exact HQ | exact HP |]. eapply leaf_vis; [exact Hst | exact L].
        -- exfalso. exact (Hnx code mo' Hxt).
    + intros tr. split.
      * intros [i Hi]. destruct i as [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn in Hi.
        -- destruct (Hk rsp mo' evs Hst) as [-> _].
           destruct Hi as [Hp | (tr' & -> & Ht)]; [apply is_prefix_nil_r in Hp; subst tr; left; reflexivity|].
           cbn. destruct Ht as [-> | (r & mo'' & L & HKr)]; [left; reflexivity|].
           right. exists r, mo''. split; [eapply leaf_vis; [exact Hst | exact L] | exact HKr].
        -- exfalso. exact (Hnx code mo' Hxt).
      * intros [-> | (r & mo'' & L & HKr)].
        -- exists (inl (exist _ (rsp0, mo0, evs0) H0)). cbn. left. apply is_prefix_nil.
        -- inversion L; subst.
           match goal with Hst : (nstep_cfg acfg) _ _ ?rsp ?mo1 ?evs, Hl : leaf _ _ _ _ |- _ =>
             exists (inl (exist _ (rsp, mo1, evs) Hst)); cbn;
             destruct (Hk rsp mo1 evs Hst) as [-> _]; right; exists tr; split; [reflexivity|];
             right; exists r, mo''; auto end.
Qed.

(* [comment removed for export] *)
End ImplSplit.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BridgeLeaf.
Variable segs : list Segment.
Let NS := nodes_sound_cfg acfg segs.

Theorem impl_trz_realizes_leaf : forall {R} (t : itree node R) Q ms mo (K : R -> Model -> TSet) T,
  impl segs (at_node segs) t Q ms ->
  trz node (nstep_cfg acfg) nexit minv nsafe t mo K T ->
  m_halted mo = None -> minv mo ->
  (forall r ms' mo', Q r ms' -> leaf t mo r mo' -> m_halted mo' = None -> minv mo' ->
     realizes_cfg acfg segs (mkCfg ms' mo') (K r mo')) ->
  realizes_cfg acfg segs (mkCfg ms mo) T.
Proof.
  intros R t Q ms mo K T Himpl Htrz. revert ms Himpl.
  induction Htrz as [r mo K | n k mo K TT i0 Hminv Hsafe Hk IH Hex | t mo K T T' Ht IH Heq];
    intros ms Himpl Hh Hmi HK.
  - cbn in Himpl. destruct Himpl as (ms' & Hms & HQ).
    eapply (rz_msteps_lib_cfg acfg segs); [exact Hh | apply (nsc_lazy _ _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    apply HK; [exact HQ | constructor | exact Hh | exact Hmi].
  - cbn in Himpl. destruct Himpl as (ms1 & Hms & Hat & Hcont).
    eapply (rz_msteps_lib_cfg acfg segs); [exact Hh | apply (nsc_lazy _ _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    apply (rz_node_cfg acfg segs (mkCfg ms1 mo) (ans_idx node (nstep_cfg acfg) nexit n mo) (ans_evs node (nstep_cfg acfg) nexit n mo)
             (nxcfg node (nstep_cfg acfg) nexit n mo ms1) TT i0).
    + apply (node_ok_at_cfg acfg node segs (at_node segs) (nstep_cfg acfg) nexit minv nsafe NS); assumption.
    + intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn.
      * destruct (nsc_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hmi Hsafe Hst) as (Hh' & Hmi' & _).
        apply (IH rsp mo' evs Hst (nret ms1 rsp) (Hcont rsp) Hh' Hmi').
        intros r ms' mo'' HQ L. apply HK; [exact HQ|]. eapply leaf_vis; [exact Hst | exact L].
      * rewrite (Hex code mo' Hxt). apply rz_halt_cfg. cbn.
        destruct (nsc_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hmi Hsafe Hxt) as (Hh' & _).
        rewrite Hh'. discriminate.
  - eapply rz_conseq_cfg; [apply IH; assumption | exact Heq].
Qed.
End BridgeLeaf.
End RC__1.
