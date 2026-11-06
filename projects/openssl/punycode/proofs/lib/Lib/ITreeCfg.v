(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import CfgStep CatSim ShapeAlg SpinAlg.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import PropExec MState Mem Exec ITree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section ITreeCfg.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.

Local Notation itree := (ITree.itree node).
Local Notation impl := (@ITree.impl node segs at_node).
Local Notation ttrace := (@ITree.ttrace node nstep nexit).
Local Notation tsafe := (@ITree.tsafe node nstep nsafe).
Local Notation leaves_unreachable_m := (@ITree.leaves_unreachable_m node nstep).

(* [comment removed for export] *)
Record node_sound_cfg : Prop := {
  nsc_lazy : forall mo, minv mo -> m_vm_lazy mo = [];
  nsc_complete : forall n ms mo evs X, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      sstep_cfg segs kit_cfg (mkCfg ms mo) evs X ->
        (exists rsp mo', X = SNext (mkCfg (nret ms rsp) mo') /\ nstep n mo rsp mo' evs)
     \/ (exists code mo', X = SNext (mkCfg ms mo') /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')]);
  nsc_sound : forall n ms mo rsp mo' evs, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nstep n mo rsp mo' evs ->
      m_halted mo' = None /\ minv mo'
      /\ sstep_cfg segs kit_cfg (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo'));
  nsc_exit : forall n ms mo code mo', at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nexit n mo code mo' ->
      m_halted mo' = Some code /\ sstep_cfg segs kit_cfg (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo'));
  nsc_progress : forall n ms mo, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      (exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo')
}.

(* [comment removed for export] *)
Definition tree_shape {R} (t : itree R) (mo : Model) : TSet :=
  fun tr => exists full, ttrace t mo full /\ is_prefix tr full.

Definition tree_at {R} (t : itree R) (Q : R -> machine_state -> Prop) (ms : machine_state) (mo : Model) : Prop :=
  impl t Q ms /\ leaves_unreachable_m t mo /\ m_halted mo = None /\ minv mo /\ tsafe t mo.

Hypothesis NS : node_sound_cfg.

Lemma tree_at_step : forall {R} n (k : resp -> itree R) Q ms1 mo rsp mo' evs,
  at_node n ms1 -> (forall rsp, impl (k rsp) Q (nret ms1 rsp)) ->
  leaves_unreachable_m (Vis n k) mo -> m_halted mo = None -> minv mo -> tsafe (Vis n k) mo ->
  nstep n mo rsp mo' evs ->
  tree_at (k rsp) Q (nret ms1 rsp) mo'.
Proof.
  intros R n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst.
  destruct (nsc_sound NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (Hh' & Hinv' & _).
  split; [apply Hk|]. split; [eapply ITree.leaves_unreachable_m_step; eassumption|].
  split; [exact Hh'|]. split; [exact Hinv'|]. eapply ITree.tsafe_step; eassumption.
Qed.

Lemma ttrace_exists : forall {R} (t : itree R) Q ms mo, tree_at t Q ms mo -> exists full, ttrace t mo full.
Proof.
  intros R t. induction t as [r|n k IH]; intros Q ms mo HT.
  - destruct HT as (_ & Hl & _). destruct (ITree.leaves_unreachable_m_ret node nstep r mo Hl).
  - destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    destruct (nsc_progress NS n ms1 mo Hat Hh Hinv (proj1 Hsf)) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
    + pose proof (tree_at_step n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as HT'.
      destruct (IH rsp Q (nret ms1 rsp) mo' HT') as (full' & Hfull').
      exists (evs ++ full'). cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
    + exists [ExitEv code (m_fs mo')]. cbn. left. exists code, mo'. split; [assumption|reflexivity].
Qed.

Lemma msteps_CatSim : forall ms ms', Exec.msteps segs ms ms' -> CatSim.msteps segs ms ms'.
Proof.
  induction 1 as [ms|ms ms1 ms2 [Hsvc Hst] _ IH]; [apply mst_refl|]. eapply mst_step; [exact Hsvc| exact Hst| exact IH].
Qed.

(* [comment removed for export] *)
Local Definition nidx (n : node) (mo : Model) : Type :=
  ({x : resp * Model * list event | nstep n mo (fst (fst x)) (snd (fst x)) (snd x)}
   + {y : word * Model | nexit n mo (fst y) (snd y)})%type.

Theorem impl_realizes : forall {R} (t : itree R) Q ms mo,
  tree_at t Q ms mo -> realizes segs (mkCfg ms mo) (tree_shape t mo).
Proof.
  intros R t. induction t as [r|n k IH]; intros Q ms mo HT.
  - destruct HT as (_ & Hl & _). destruct (ITree.leaves_unreachable_m_ret node nstep r mo Hl).
  - pose proof HT as (Ht & Hl & Hh & Hinv & Hsf).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    apply (rz_msteps segs ms ms1 mo _ Hh (nsc_lazy NS mo Hinv) (msteps_CatSim ms ms1 Hm)).
    (* [comment removed for export] *)
    set (evs := fun i : nidx n mo => match i with
                  | inl x => snd (proj1_sig x)
                  | inr y => [ExitEv (fst (proj1_sig y)) (m_fs (snd (proj1_sig y)))] end).
    set (nx := fun i : nidx n mo => match i with
                  | inl x => mkCfg (nret ms1 (fst (fst (proj1_sig x)))) (snd (fst (proj1_sig x)))
                  | inr y => mkCfg ms1 (snd (proj1_sig y)) end).
    set (T := fun i : nidx n mo => match i with
                  | inl x => tree_shape (k (fst (fst (proj1_sig x)))) (snd (fst (proj1_sig x)))
                  | inr y => t_nil end).
    assert (Hnode : node_ok segs (mkCfg ms1 mo) (nidx n mo) evs nx).
    { split.
      - intros [[[[rsp mo'] ev] Hst]|[[code mo'] Hex]]; cbn [evs nx proj1_sig fst snd] in *.
        + exact (proj2 (proj2 (nsc_sound NS n ms1 mo rsp mo' ev Hat Hh Hinv (proj1 Hsf) Hst))).
        + exact (proj2 (nsc_exit NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex)).
      - intros e st Hss.
        destruct (nsc_complete NS n ms1 mo e st Hat Hh Hinv (proj1 Hsf) Hss)
          as [(rsp & mo' & -> & Hst)|(code & mo' & -> & Hex & ->)].
        + exists (inl (exist _ (rsp, mo', e) Hst)). split; reflexivity.
        + exists (inr (exist _ (code, mo') Hex)). split; reflexivity. }
    assert (Hcont : forall i, realizes segs (nx i) (T i)).
    { intros [[[[rsp mo'] ev] Hst]|[[code mo'] Hex]]; cbn [nx T proj1_sig fst snd] in *.
      - apply (IH rsp Q). exact (tree_at_step n k Q ms1 mo rsp mo' ev Hat Hk Hl Hh Hinv Hsf Hst).
      - apply rz_halt. cbn [cfg_model]. rewrite (proj1 (nsc_exit NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex)). discriminate. }
    assert (Heq : t_eq (t_alt (fun i => t_emit (evs i) (T i))) (tree_shape (Vis n k) mo)).
    { intros tr. unfold t_alt, tree_shape. split.
      - intros ([[[[rsp mo'] ev] Hst]|[[code mo'] Hex]] & Hi); cbn [evs T proj1_sig fst snd] in Hi.
        + pose proof (tree_at_step n k Q ms1 mo rsp mo' ev Hat Hk Hl Hh Hinv Hsf Hst) as HT'.
          destruct Hi as [Hp|(tr' & -> & (full' & Hf' & Hp'))].
          * destruct (ttrace_exists (k rsp) Q _ mo' HT') as (full' & Hf').
            exists (ev ++ full'). split; [cbn; right; exists rsp, mo', ev, full'; repeat split; assumption|].
            apply is_prefix_app_r. exact Hp.
          * exists (ev ++ full'). split; [cbn; right; exists rsp, mo', ev, full'; repeat split; assumption|].
            apply ITree.is_prefix_app_l. exact Hp'.
        + exists [ExitEv code (m_fs mo')]. split; [cbn; left; exists code, mo'; split; [exact Hex| reflexivity]|].
          destruct Hi as [Hp|(tr' & -> & ->)]; [exact Hp| rewrite app_nil_r; apply is_prefix_refl].
      - intros (full & Hf & Hp). cbn in Hf.
        destruct Hf as [(code & mo' & Hex & ->)|(rsp & mo' & ev & tr' & Hst & Hf' & ->)].
        + exists (inr (exist _ (code, mo') Hex)). cbn [evs T proj1_sig fst snd]. left. exact Hp.
        + exists (inl (exist _ (rsp, mo', ev) Hst)). cbn [evs T proj1_sig fst snd].
          apply is_prefix_app_split in Hp as [Hp|(b' & -> & Hp)]; [left; exact Hp|].
          right. exists b'. split; [reflexivity|]. exists tr'. split; assumption. }
    destruct (nsc_progress NS n ms1 mo Hat Hh Hinv (proj1 Hsf)) as [(rsp & mo' & ev & Hst)|(code & mo' & Hex)].
    + eapply rz_conseq; [|exact Heq].
      exact (rz_node segs _ (nidx n mo) evs nx T (inl (exist _ (rsp, mo', ev) Hst)) Hnode Hcont).
    + eapply rz_conseq; [|exact Heq].
      exact (rz_node segs _ (nidx n mo) evs nx T (inr (exist _ (code, mo') Hex)) Hnode Hcont).
Qed.

(* [comment removed for export] *)
Corollary impl_srealizes : forall {R} (t : itree R) Q ms mo,
  tree_at t Q ms mo -> srealizes segs (mkCfg ms mo) (tree_shape t mo).
Proof. intros R t Q ms mo HT. apply srealizes_of_realizes. exact (impl_realizes t Q ms mo HT). Qed.

End ITreeCfg.
