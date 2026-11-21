(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import PropExec MState Mem Exec ITree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import Exc.

Section Halts.

Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.

Let NSound := node_sound node segs at_node nstep nexit minv nsafe.
Let TreeAt := fun {R} (t : itree node R) Q ms mo => tree_at segs at_node nstep minv nsafe t Q ms mo.

Lemma sstep_exit_event_not_killed : forall c code fs c',
  sstep segs c [ExitEv code fs] (SNext c') ->
  m_halted (cfg_model c') = Some code ->
  m_killed (cfg_model c') = None.
Proof.
  intros c code fs c' Hss Hh.
  destruct (sstep_next_halts_by_exit segs c [ExitEv code fs] c' Hss)
    as [Hnone | [(evs0 & code' & Hevs & Hh' & Hk) | (evs0 & sig & Hevs & Hk)]].
  - congruence.
  - exact Hk.
  - exfalso. destruct evs0 as [|e evs0]; cbn in Hevs.
    + discriminate Hevs.
    + injection Hevs as He Htl. destruct evs0; discriminate Htl.
Qed.

Theorem tree_at_must_exit : NSound -> forall (S : list word) {R} (t : itree node R) Q ms mo,
  (forall n mo1 code mo2, nexit n mo1 code mo2 -> In code S) ->
  TreeAt t Q ms mo ->
  must_exit_in_at segs S (mkCfg ms mo).
Proof.
  intros NS S R t. induction t as [r | n k IH]; intros Q ms mo HS HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret node nstep r mo Hl).
  - pose proof HT as HT0. destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    assert (MAIN : forall msx, msteps segs msx ms1 -> must_exit_in_at segs S (mkCfg msx mo)).
    { intros msx Hmx. induction Hmx as [msx | msx msa msb Hstep Hrest IHm].
      -
        assert (HTx : TreeAt (Vis n k) Q msx mo).
        { split; [| split; [exact Hl | split; [exact Hh | split; [exact Hinv | exact Hsf]]]].
          cbn. exists msx. split; [apply msteps_refl |]. split; [exact Hat | exact Hk]. }
        apply must_exit_in_at_running.
        + exact Hh.
        + destruct (ns_progress _ _ _ _ _ _ _ NS n msx mo Hat Hh Hinv (proj1 Hsf))
            as [(rsp & mo' & evs & Hst) | (code & mo' & Hex)].
          * destruct (ns_sound _ _ _ _ _ _ _ NS n msx mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (_ & _ & Hss).
            exists evs, (SNext (mkCfg (nret msx rsp) mo')). exact Hss.
          * destruct (ns_exit _ _ _ _ _ _ _ NS n msx mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (_ & Hss).
            exists [ExitEv code (m_fs mo')], (SNext (mkCfg msx mo')). exact Hss.
        + intros evs Herr.
          destruct (impl_sstep_inv _ _ _ _ _ _ _ NS (Vis n k) Q msx mo evs SError HTx Herr)
            as [(ms' & E & _) | [(n' & k' & rsp & mo' & _ & _ & E & _) | (n' & k' & code & mo' & _ & _ & E & _)]];
            discriminate E.
        + intros evs c' Hss.
          destruct (impl_sstep_inv _ _ _ _ _ _ _ NS (Vis n k) Q msx mo evs (SNext c') HTx Hss)
            as [(ms' & E & _ & Hms & _) | [(n' & k' & rsp & mo' & Et & _ & E & Hst & HT') | (n' & k' & code & mo' & Et & _ & E & Hex & Hevs & Hh')]].
          * exfalso. pose proof (mstep_not_svc segs msx ms' Hms) as Hn.
            exact (ns_pending _ _ _ _ _ _ _ NS n msx Hat Hn).
          * injection Et as En Ek. subst n' k'. injection E as ->.
            apply (IH rsp Q (nret msx rsp) mo' HS HT').
          * injection Et as En Ek. subst n' k'. injection E as ->. subst evs.
            apply (must_exit_in_at_halted segs S (mkCfg msx mo') code).
            -- exact Hh'.
            -- exact (HS n mo code mo' Hex).
            -- exact (sstep_exit_event_not_killed (mkCfg msx mo) code (m_fs mo') (mkCfg msx mo') Hss Hh').
      -
        assert (HTx : TreeAt (Vis n k) Q msx mo).
        { split; [| split; [exact Hl | split; [exact Hh | split; [exact Hinv | exact Hsf]]]].
          cbn. exists msb. split; [eapply msteps_cons; eassumption |]. split; [exact Hat | exact Hk]. }
        apply must_exit_in_at_running.
        + exact Hh.
        + exists [], (SNext (mkCfg msa mo)). apply mstep_sstep; [exact Hh | exact (ns_nolazy _ _ _ _ _ _ _ NS mo Hinv) | exact Hstep].
        + intros evs Herr.
          destruct (impl_sstep_inv _ _ _ _ _ _ _ NS (Vis n k) Q msx mo evs SError HTx Herr)
            as [(ms' & E & _) | [(n' & k' & rsp & mo' & _ & _ & E & _) | (n' & k' & code & mo' & _ & _ & E & _)]];
            discriminate E.
        + intros evs c' Hss.
          destruct (impl_sstep_inv _ _ _ _ _ _ _ NS (Vis n k) Q msx mo evs (SNext c') HTx Hss)
            as [(ms' & E & _ & Hms & _) | [(n' & k' & rsp & mo' & Et & Hat' & _) | (n' & k' & code & mo' & Et & Hat' & _)]].
          * injection E as ->. rewrite (mstep_det segs msx ms' msa Hms Hstep). exact (IHm Hm Hat Hk).
          * exfalso. exact (ns_pending _ _ _ _ _ _ _ NS n' msx Hat' (mstep_not_svc segs msx msa Hstep)).
          * exfalso. exact (ns_pending _ _ _ _ _ _ _ NS n' msx Hat' (mstep_not_svc segs msx msa Hstep)). }
    exact (MAIN ms Hm).
Qed.
End Halts.

Section HaltsRun.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.

Theorem impl_run_must_exit2 :
  node_sound node segs at_node nstep nexit minv nsafe ->
  forall (S : list word) {R} (t : itree node R) Q ms mo,
  impl segs at_node t Q ms -> leaves_unreachable_m nstep t mo -> m_halted mo = None -> minv mo ->
  tsafe nstep nsafe t mo ->
  (forall n mo1 code mo2, nexit n mo1 code mo2 -> In code S) ->
  must_exit_in_at segs S (mkCfg ms mo).
Proof.
  intros NS S R t Q ms mo Ht Hl Hh Hinv Hsf HS.
  apply (tree_at_must_exit node segs at_node nstep nexit minv nsafe NS S t Q ms mo HS).
  split; [exact Ht | split; [exact Hl | split; [exact Hh | split; [exact Hinv | exact Hsf]]]].
Qed.
End HaltsRun.
