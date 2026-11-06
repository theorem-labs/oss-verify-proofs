(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Exec ITree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section ITreeHalts.
Variable node : Type.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Hypothesis NS : node_sound node segs cfg at_node nstep nexit minv nsafe.
Variable S : list word.

(* [comment removed for export] *)
Definition exits_in (c : config) : Prop :=
  forall tr c', star_cfg segs cfg c tr c' -> forall tr0 code fs, tr = tr0 ++ [ExitEv code fs] -> In code S.

Lemma exits_in_step : forall c evs c', exits_in c -> sstep_cfg segs cfg c evs (SNext c') -> exits_in c'.
Proof.
  intros c evs c' H Hss tr c'' Hst tr0 code fs E.
  apply (H (evs ++ tr) c'' (star_cfg_step segs cfg c evs c' tr c'' Hss Hst) (evs ++ tr0) code fs).
  rewrite E, app_assoc. reflexivity.
Qed.

Lemma at_node_must_exit : forall {R} (n : node) (k : resp -> itree node R) (Q : R -> machine_state -> Prop) ms1 mo,
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> tree_at segs at_node nstep minv nsafe (k rsp) Q (nret ms1 rsp) mo' ->
       exits_in (mkCfg (nret ms1 rsp) mo') ->
       must_exit_in_at_cfg cfg segs S (mkCfg (nret ms1 rsp) mo')) ->
  at_node n ms1 -> (forall rsp, impl segs at_node (k rsp) Q (nret ms1 rsp)) ->
  leaves_unreachable_m nstep (Vis n k) mo -> m_halted mo = None -> minv mo -> tsafe nstep nsafe (Vis n k) mo ->
  exits_in (mkCfg ms1 mo) ->
  must_exit_in_at_cfg cfg segs S (mkCfg ms1 mo).
Proof.
  intros R n k Q ms1 mo IHk Hat Hk Hl Hh Hinv Hsf Hc.
  apply must_exit_in_at_cfg_running; [exact Hh | | |].
  - destruct (ns_progress _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hinv (proj1 Hsf)) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
    + destruct (ns_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (_ & _ & Hss).
      eexists; eexists; exact Hss.
    + destruct (ns_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (_ & Hss).
      eexists; eexists; exact Hss.
  - intros evs Herr.
    destruct (ns_complete _ _ _ _ _ _ _ _ NS n ms1 mo evs SError Hat Hh Hinv (proj1 Hsf) Herr)
      as [(rsp & mo' & HX & _)|(code & mo' & HX & _)]; discriminate HX.
  - intros evs c' Hss.
    destruct (ns_complete _ _ _ _ _ _ _ _ NS n ms1 mo evs (SNext c') Hat Hh Hinv (proj1 Hsf) Hss)
      as [(rsp & mo' & HX & Hst)|(code & mo' & HX & Hex & Hevs)]; injection HX as ->.
    + apply (IHk rsp mo' evs Hst).
      * exact (proj1 (tree_at_step node segs cfg at_node nstep nexit minv nsafe NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst)).
      * exact (exits_in_step _ _ _ Hc Hss).
    + destruct (ns_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (Hh' & _).
      assert (Hin : In code S).
      { apply (Hc [ExitEv code (m_fs mo')] (mkCfg ms1 mo')) with (tr0 := []) (fs := m_fs mo'); [| reflexivity].
        rewrite <- (app_nil_r [ExitEv code (m_fs mo')]). rewrite <- Hevs at 1.
        apply (star_cfg_step segs cfg _ evs (mkCfg ms1 mo') [] _ Hss). apply star_cfg_refl. }
      apply (must_exit_in_at_cfg_halted cfg segs S (mkCfg ms1 mo') code Hh' Hin).
      destruct (sstep_cfg_next_halts_by_exit segs cfg _ _ _ Hss)
        as [Hn | [(evs0 & code' & _ & _ & Hk') | (evs0 & sig & Hev & _)]].
      * cbn in Hn. congruence.
      * exact Hk'.
      * exfalso. rewrite Hevs in Hev.
        assert (Hl2 : last [ExitEv code (m_fs mo')] (ExitEv code (m_fs mo')) = last (evs0 ++ [KillEv sig (m_fs (cfg_model (mkCfg ms1 mo')))]) (ExitEv code (m_fs mo')))
          by (rewrite Hev; reflexivity).
        rewrite last_last in Hl2. cbn in Hl2. discriminate Hl2.
Qed.

Theorem impl_must_exit : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) ms mo,
  tree_at segs at_node nstep minv nsafe t Q ms mo -> exits_in (mkCfg ms mo) ->
  must_exit_in_at_cfg cfg segs S (mkCfg ms mo).
Proof.
  intros R t. induction t as [r|n k IH]; intros Q ms mo HT Hc.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret node nstep r mo Hl).
  - destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    induction Hm as [ms|ms msa msb H1 H2 IHm].
    + apply (at_node_must_exit n k Q ms mo); try assumption.
      intros rsp mo' evs Hst HT' Hc'. exact (IH rsp Q _ mo' HT' Hc').
    + apply must_exit_in_at_cfg_running; [exact Hh | | |].
      * eexists; eexists. exact (mstep_sstep segs cfg ms msa mo Hh (ns_lazy _ _ _ _ _ _ _ _ NS mo Hinv) H1).
      * intros evs Herr.
        destruct (sstep_mstep_inv segs cfg ms mo msa evs SError (ns_lazy _ _ _ _ _ _ _ _ NS mo Hinv) H1 Herr) as (_ & HX). discriminate HX.
      * intros evs c' Hss.
        destruct (sstep_mstep_inv segs cfg ms mo msa evs (SNext c') (ns_lazy _ _ _ _ _ _ _ _ NS mo Hinv) H1 Hss) as (_ & HX).
        injection HX as ->. apply IHm; try assumption. exact (exits_in_step _ _ _ Hc Hss).
Qed.

End ITreeHalts.
