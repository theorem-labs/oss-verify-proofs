(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree ITreeCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Export ImplRz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Leaf.
Variable node : Type.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.

(* [comment removed for export] *)
Inductive leaf {R : Type} : itree node R -> Model -> R -> Model -> Prop :=
| leaf_ret : forall r mo, leaf (Ret r) mo r mo
| leaf_vis : forall n k mo rsp mo1 evs r mo',
    nstep n mo rsp mo1 evs -> leaf (k rsp) mo1 r mo' -> leaf (Vis n k) mo r mo'.

Lemma leaf_ret_inv : forall {R} (r0 r : R) mo mo', leaf (Ret r0) mo r mo' -> r = r0 /\ mo' = mo.
Proof. intros R r0 r mo mo' H. inversion H; subst; auto. Qed.

Lemma leaf_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo r mo'',
  leaf (bind node t f) mo r mo'' <-> exists a mo', leaf t mo a mo' /\ leaf (f a) mo' r mo''.
Proof.
  intros A B t; induction t as [a | n k IH]; intros f mo r mo''; cbn.
  - split.
    + intros H. exists a, mo. split; [constructor | exact H].
    + intros (a' & mo' & L & H). apply leaf_ret_inv in L as [-> ->]. exact H.
  - split.
    + intros H. inversion H; subst.
      match goal with Hst : nstep _ _ ?rsp ?mo1 ?evs, Hl : leaf _ _ _ _ |- _ =>
        apply IH in Hl as (a & mo' & L1 & L2); exists a, mo'; split; [eapply leaf_vis; [exact Hst | exact L1] | exact L2] end.
    + intros (a & mo' & L1 & L2). inversion L1; subst.
      match goal with Hst : nstep _ _ ?rsp ?mo1 ?evs, Hl : leaf _ _ _ _ |- _ =>
        eapply leaf_vis; [exact Hst|]; apply IH; exists a, mo'; split; [exact Hl | exact L2] end.
Qed.

(* [comment removed for export] *)
Lemma tsil_leaf : forall nexit nsafe {R} (t : itree node R) mo (P : R -> Model -> Prop) r mo',
  ImplRz.tsil node nstep nexit nsafe t mo P -> leaf t mo r mo' -> P r mo'.
Proof.
  intros nexit nsafe R t; induction t as [r0 | n k IH]; intros mo P r mo' Hs L.
  - apply leaf_ret_inv in L as [-> ->]. exact Hs.
  - inversion L; subst. cbn in Hs. destruct Hs as (_ & _ & Hk).
    match goal with Hst : nstep _ _ ?rsp ?mo1 ?evs, Hl : leaf _ _ _ _ |- _ =>
      eapply IH; [exact (proj2 (Hk _ _ _ Hst)) | exact Hl] end.
Qed.
End Leaf.
Arguments leaf {node} nstep {R} t mo r mo'.

Section Mono.
Variable node : Type.
Variables nstep nstep' : node -> Model -> resp -> Model -> list event -> Prop.
Hypothesis SUB : forall n mo rsp mo' evs, nstep' n mo rsp mo' evs -> nstep n mo rsp mo' evs.

Lemma leaf_monotone : forall {R} (t : itree node R) mo r mo',
  leaf nstep' t mo r mo' -> leaf nstep t mo r mo'.
Proof.
  intros R t mo r mo' H; induction H as [r mo | n k mo rsp mo1 evs r mo' Hst Hl IH].
  - constructor.
  - eapply leaf_vis; [apply SUB; exact Hst | exact IH].
Qed.

(* [comment removed for export] *)
Lemma tsil_antitone : forall nexit nsafe {R} (t : itree node R) mo (P : R -> Model -> Prop),
  ImplRz.tsil node nstep nexit nsafe t mo P -> ImplRz.tsil node nstep' nexit nsafe t mo P.
Proof.
  intros nexit nsafe R t; induction t as [r | n k IH]; intros mo P H; cbn in *.
  - exact H.
  - destruct H as (Hsafe & Hnx & Hk). split; [exact Hsafe|]. split; [exact Hnx|].
    intros rsp mo' evs Hst. destruct (Hk rsp mo' evs (SUB _ _ _ _ _ Hst)) as [E H'].
    split; [exact E | apply IH; exact H'].
Qed.
End Mono.

Section Conj.
Variable node : Type.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable nsafe : node -> Model -> Prop.

Lemma tsil_conj : forall {R} (t : itree node R) mo (P1 P2 : R -> Model -> Prop),
  ImplRz.tsil node nstep nexit nsafe t mo P1 -> ImplRz.tsil node nstep nexit nsafe t mo P2 ->
  ImplRz.tsil node nstep nexit nsafe t mo (fun r mo' => P1 r mo' /\ P2 r mo').
Proof.
  intros R t; induction t as [r | n k IH]; intros mo P1 P2 H1 H2; cbn in *.
  - split; assumption.
  - destruct H1 as (Hsafe & Hnx & Hk1). destruct H2 as (_ & _ & Hk2).
    split; [exact Hsafe|]. split; [exact Hnx|].
    intros rsp mo' evs Hst. destruct (Hk1 _ _ _ Hst) as [E H1']. destruct (Hk2 _ _ _ Hst) as [_ H2'].
    split; [exact E | apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma tsil_leaf_conj : forall {R} (t : itree node R) mo (P : R -> Model -> Prop),
  ImplRz.tsil node nstep nexit nsafe t mo P ->
  ImplRz.tsil node nstep nexit nsafe t mo (fun r mo' => P r mo' /\ leaf nstep t mo r mo').
Proof.
  intros R t; induction t as [r | n k IH]; intros mo P H; cbn in *.
  - split; [exact H | constructor].
  - destruct H as (Hsafe & Hnx & Hk). split; [exact Hsafe|]. split; [exact Hnx|].
    intros rsp mo' evs Hst. destruct (Hk _ _ _ Hst) as [E H']. split; [exact E|].
    eapply ImplRz.tsil_mono; [apply IH; exact H'|].
    intros r mo'' [HP HL]. split; [exact HP | eapply leaf_vis; [exact Hst | exact HL]].
Qed.
End Conj.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ImplRzCfg.

Variable cfg : SpuriousCfg.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.   (* [comment removed for export] *)
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Hypothesis NS : node_sound_cfg cfg node segs at_node nstep nexit minv nsafe.

Local Abbreviation itreeN := (itree node).
Local Abbreviation implN := (impl segs at_node).
Local Abbreviation realizesC := (realizes_cfg cfg segs).
Local Abbreviation trzN := (trz node nstep nexit minv nsafe).
Local Abbreviation tsilN := (ImplRz.tsil node nstep nexit nsafe).
Local Abbreviation ans_idxN := (ans_idx node nstep nexit).
Local Abbreviation ans_evsN := (ans_evs node nstep nexit).
Local Abbreviation nxcfgN := (nxcfg node nstep nexit).

Lemma rz_msteps_lib_cfg : forall ms ms' mo T,
  m_halted mo = None -> m_vm_lazy mo = [] ->
  Exec.msteps segs ms ms' ->
  realizesC (mkCfg ms' mo) T -> realizesC (mkCfg ms mo) T.
Proof.
  intros ms ms' mo T Hh Hl Hms. induction Hms as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH]; intros Hc.
  - exact Hc.
  - eapply rz_step_cfg; [exact Hh | exact Hl | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

Lemma node_ok_at_cfg : forall n ms1 mo,
  at_node n ms1 -> m_halted mo = None -> minv mo -> nsafe n mo ->
  node_ok_cfg cfg segs (mkCfg ms1 mo) (ans_idxN n mo) (ans_evsN n mo) (nxcfgN n mo ms1).
Proof.
  intros n ms1 mo Hat Hh Hmi Hsafe. split.
  - intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn.
    + destruct (nsc_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hmi Hsafe Hst) as (_ & _ & Hss). exact Hss.
    + destruct (nsc_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hmi Hsafe Hxt) as (_ & Hss). exact Hss.
  - intros e st Hss.
    destruct (nsc_complete _ _ _ _ _ _ _ _ NS n ms1 mo e st Hat Hh Hmi Hsafe Hss)
      as [(rsp & mo' & -> & Hst) | (code & mo' & -> & Hxt & ->)].
    + exists (inl (exist _ (rsp, mo', e) Hst)). split; reflexivity.
    + exists (inr (exist _ (code, mo') Hxt)). split; reflexivity.
Qed.

Lemma ans_idx_inh_cfg : forall n ms1 mo,
  at_node n ms1 -> m_halted mo = None -> minv mo -> nsafe n mo -> inhabited (ans_idxN n mo).
Proof.
  intros n ms1 mo Hat Hh Hmi Hsafe.
  destruct (nsc_progress _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hmi Hsafe)
    as [(rsp & mo' & evs & H) | (code & mo' & H)].
  - exact (inhabits (inl (exist _ (rsp, mo', evs) H))).
  - exact (inhabits (inr (exist _ (code, mo') H))).
Qed.

(* [comment removed for export] *)
Theorem impl_trz_realizes_leaf_cfg : forall {R} (t : itreeN R) Q ms mo (K : R -> Model -> TSet) T,
  implN t Q ms ->
  trzN t mo K T ->
  m_halted mo = None -> minv mo ->
  (forall r ms' mo', Q r ms' -> leaf nstep t mo r mo' -> m_halted mo' = None -> minv mo' ->
     realizesC (mkCfg ms' mo') (K r mo')) ->
  realizesC (mkCfg ms mo) T.
Proof.
  intros R t Q ms mo K T Himpl Htrz. revert ms Himpl.
  induction Htrz as [r mo K | n k mo K TT i0 Hminv Hsafe Hk IH Hex | t mo K T T' Ht IH Heq];
    intros ms Himpl Hh Hmi HK.
  - (* [comment removed for export] *)
    cbn in Himpl. destruct Himpl as (ms' & Hms & HQ).
    eapply rz_msteps_lib_cfg; [exact Hh | apply (nsc_lazy _ _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    apply HK; [exact HQ | constructor | exact Hh | exact Hmi].
  - (* [comment removed for export] *)
    cbn in Himpl. destruct Himpl as (ms1 & Hms & Hat & Hcont).
    eapply rz_msteps_lib_cfg; [exact Hh | apply (nsc_lazy _ _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    apply (rz_node_cfg cfg segs (mkCfg ms1 mo) (ans_idxN n mo) (ans_evsN n mo) (nxcfgN n mo ms1) TT i0).
    + apply node_ok_at_cfg; assumption.
    + intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn.
      * destruct (nsc_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hmi Hsafe Hst) as (Hh' & Hmi' & _).
        apply (IH rsp mo' evs Hst (nret ms1 rsp) (Hcont rsp) Hh' Hmi').
        intros r ms' mo'' HQ HL Hh'' Hmi''. apply HK; [exact HQ | | exact Hh'' | exact Hmi''].
        eapply leaf_vis; [exact Hst | exact HL].
      * rewrite (Hex code mo' Hxt).
        apply rz_halt_cfg. cbn.
        destruct (nsc_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hmi Hsafe Hxt) as (Hh' & _).
        rewrite Hh'. discriminate.
  - (* [comment removed for export] *)
    eapply rz_conseq_cfg; [apply IH; assumption | exact Heq].
Qed.

Theorem impl_trz_realizes_cfg : forall {R} (t : itreeN R) Q ms mo K T,
  implN t Q ms ->
  trzN t mo K T ->
  m_halted mo = None -> minv mo ->
  (forall r ms' mo', Q r ms' -> m_halted mo' = None -> minv mo' ->
     realizesC (mkCfg ms' mo') (K r mo')) ->
  realizesC (mkCfg ms mo) T.
Proof.
  intros R t Q ms mo K T Himpl Htrz Hh Hmi HK.
  eapply impl_trz_realizes_leaf_cfg; [exact Himpl | exact Htrz | exact Hh | exact Hmi |].
  intros r ms' mo' HQ _ Hh' Hmi'. exact (HK r ms' mo' HQ Hh' Hmi').
Qed.

(* [comment removed for export] *)
Theorem impl_tsil_realizes_leaf_cfg : forall {R} (t : itreeN R) Q ms mo P (T : TSet),
  implN t Q ms ->
  tsilN t mo P ->
  m_halted mo = None -> minv mo ->
  T [] ->
  (forall r ms' mo', Q r ms' -> P r mo' -> leaf nstep t mo r mo' -> m_halted mo' = None -> minv mo' ->
     realizesC (mkCfg ms' mo') T) ->
  realizesC (mkCfg ms mo) T.
Proof.
  intros R t; induction t as [r | n k IH]; intros Q ms mo P T Himpl Hsil Hh Hmi HT0 HK; cbn in Himpl, Hsil.
  - destruct Himpl as (ms' & Hms & HQ).
    eapply rz_msteps_lib_cfg; [exact Hh | apply (nsc_lazy _ _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    apply (HK r ms' mo HQ Hsil); [constructor | exact Hh | exact Hmi].
  - destruct Himpl as (ms1 & Hms & Hat & Hcont).
    destruct Hsil as (Hsafe & Hnx & Hk).
    assert (Hex : exists rsp0 mo0 evs0, nstep n mo rsp0 mo0 evs0).
    { destruct (nsc_progress _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hmi Hsafe)
        as [(rsp0 & mo0 & evs0 & H0) | (code & mo' & H)]; [exists rsp0, mo0, evs0; exact H0|].
      exfalso. exact (Hnx code mo' H). }
    destruct Hex as (rsp0 & mo0 & evs0 & H0).
    eapply rz_msteps_lib_cfg; [exact Hh | apply (nsc_lazy _ _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    apply (rz_silent_cfg cfg segs (mkCfg ms1 mo) (ans_idxN n mo) (nxcfgN n mo ms1) T
             (inl (exist _ (rsp0, mo0, evs0) H0))).
    + pose proof (node_ok_at_cfg n ms1 mo Hat Hh Hmi Hsafe) as [Hc Hs]. split.
      * intros i. pose proof (Hc i) as Hi.
        destruct i as [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn in Hi |- *.
        -- destruct (Hk rsp mo' evs Hst) as [-> _]. exact Hi.
        -- exfalso. exact (Hnx code mo' Hxt).
      * intros e st Hss. destruct (Hs e st Hss) as (i & He & Hst). exists i. split; [| exact Hst].
        destruct i as [[[[rsp mo'] evs] Hn] | [[code mo'] Hxt]]; cbn in He |- *.
        -- destruct (Hk rsp mo' evs Hn) as [E _]. subst. reflexivity.
        -- exfalso. exact (Hnx code mo' Hxt).
    + intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn.
      * destruct (nsc_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hmi Hsafe Hst) as (Hh' & Hmi' & _).
        destruct (Hk rsp mo' evs Hst) as [_ Hsil'].
        apply (IH rsp Q (nret ms1 rsp) mo' P T (Hcont rsp) Hsil' Hh' Hmi' HT0).
        intros r ms' mo'' HQ HP HL Hh'' Hmi''. apply (HK r ms' mo'' HQ HP); [| exact Hh'' | exact Hmi''].
        eapply leaf_vis; [exact Hst | exact HL].
      * exfalso. exact (Hnx code mo' Hxt).
Qed.

Theorem impl_tsil_realizes_cfg : forall {R} (t : itreeN R) Q ms mo P (T : TSet),
  implN t Q ms ->
  tsilN t mo P ->
  m_halted mo = None -> minv mo ->
  T [] ->
  (forall r ms' mo', Q r ms' -> P r mo' -> m_halted mo' = None -> minv mo' ->
     realizesC (mkCfg ms' mo') T) ->
  realizesC (mkCfg ms mo) T.
Proof.
  intros R t Q ms mo P T Himpl Hsil Hh Hmi HT0 HK.
  eapply impl_tsil_realizes_leaf_cfg; [exact Himpl | exact Hsil | exact Hh | exact Hmi | exact HT0 |].
  intros r ms' mo' HQ HP _ Hh' Hmi'. exact (HK r ms' mo' HQ HP Hh' Hmi').
Qed.

End ImplRzCfg.
