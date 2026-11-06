(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree RegsEquiv.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Halts.
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
  Hypothesis Hcodes : forall n mo code mo', nexit n mo code mo' -> In code S.

  Notation MX c := (must_exit_in_at_cfg cfg segs S c).

  (* [comment removed for export] *)
  Lemma must_exit_mstep : forall ms ms' mo,
    m_halted mo = None -> m_vm_lazy mo = [] -> mstep segs ms ms' ->
    MX (mkCfg ms' mo) -> MX (mkCfg ms mo).
  Proof.
    intros ms ms' mo Hh Hlz Hm HX.
    pose proof (mi_account_step_mstep segs ms mo ms' Hlz Hm) as Hacc.
    destruct Hm as [Hsvc Hstep].
    apply must_exit_in_at_cfg_running; cbn [cfg_model].
    - exact Hh.
    - exists [], (SNext (mkCfg ms' mo)).
      apply sstep_cfg_instr; assumption.
    - intros evs Herr.
      inversion Herr; subst; cbn in *; congruence.
    - intros evs c' Hss.
      inversion Hss; subst; cbn in *; try congruence.
      all: match goal with H : mi_account_step _ _ _ = MachineOk _ |- _ => rewrite Hacc in H; inversion H; subst end; exact HX.
  Qed.

  Lemma must_exit_msteps : forall ms ms' mo,
    m_halted mo = None -> m_vm_lazy mo = [] -> msteps segs ms ms' ->
    MX (mkCfg ms' mo) -> MX (mkCfg ms mo).
  Proof.
    intros ms ms' mo Hh Hlz Hm. induction Hm as [ms|ms ms1 ms2 H1 H2 IH]; intros HX.
    - exact HX.
    - eapply must_exit_mstep; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma exit_step_not_killed : forall ms mo code mo',
    sstep_cfg segs cfg (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo')) ->
    m_halted mo' = Some code -> m_killed mo' = None.
  Proof.
    intros ms mo code mo' Hss Hh'.
    destruct (sstep_next_halts_by_exit segs _ _ _ (sstep_cfg_sub segs cfg _ _ _ Hss)) as [Hn | [(evs0 & code' & He & Hh2 & Hk) | (evs0 & sig & He & Hk)]];
      cbn [cfg_model] in *.
    - congruence.
    - exact Hk.
    - exfalso. destruct evs0 as [|e evs0]; cbn in He; [discriminate|].
      apply (f_equal (@length event)) in He. cbn in He. rewrite length_app in He. cbn in He. lia.
  Qed.

  Theorem impl_must_exit : forall {R} (t : itree node R) Q ms mo,
    impl segs at_node t Q ms -> leaves_unreachable_m nstep t mo ->
    m_halted mo = None -> minv mo -> tsafe nstep nsafe t mo ->
    MX (mkCfg ms mo).
  Proof.
    intros R t. induction t as [r|n k IH]; intros Q ms mo Ht Hl Hh Hinv Hsf.
    - destruct (leaves_unreachable_m_ret node nstep r mo Hl).
    - cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
      apply (must_exit_msteps ms ms1 mo Hh (ns_nolazy _ _ _ _ _ _ _ _ NS mo Hinv) Hm).
      pose proof (proj1 Hsf) as Hns. cbn in Hns.
      apply must_exit_in_at_cfg_running; cbn [cfg_model].
      + exact Hh.
      + destruct (ns_progress _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hinv Hns) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
        * destruct (ns_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hinv Hns Hst) as (_ & _ & Hss).
          exists evs, (SNext (mkCfg (nret ms1 rsp) mo')). exact Hss.
        * destruct (ns_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv Hns Hex) as (_ & Hss).
          exists [ExitEv code (m_fs mo')], (SNext (mkCfg ms1 mo')). exact Hss.
      + intros evs Herr.
        destruct (ns_complete _ _ _ _ _ _ _ _ NS n ms1 mo evs SError Hat Hh Hinv Hns Herr)
          as [(rsp & mo' & HX & _)|(code & mo' & HX & _)]; discriminate.
      + intros evs c' Hss.
        destruct (ns_complete _ _ _ _ _ _ _ _ NS n ms1 mo evs (SNext c') Hat Hh Hinv Hns Hss)
          as [(rsp & mo' & HX & Hst)|(code & mo' & HX & Hex & Hevs)].
        * inversion HX; subst.
          destruct (tree_at_step _ _ _ _ _ _ _ _ NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst)
            as [(Ht' & Hl' & Hh' & Hinv' & Hsf') _].
          exact (IH rsp Q (nret ms1 rsp) mo' Ht' Hl' Hh' Hinv' Hsf').
        * inversion HX; subst.
          destruct (ns_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv Hns Hex) as (Hh' & Hss').
          apply must_exit_in_at_cfg_halted with (code := code); cbn [cfg_model].
          -- exact Hh'.
          -- exact (Hcodes _ _ _ _ Hex).
          -- exact (exit_step_not_killed ms1 mo code mo' Hss' Hh').
  Qed.

  (* [comment removed for export] *)
  Corollary impl_must_exit_lu : forall {R} (t : itree node R) ms mo,
    leaves_unreachable node segs at_node t ms ->
    m_halted mo = None -> minv mo -> tsafe nstep nsafe t mo ->
    MX (mkCfg ms mo).
  Proof.
    intros R t ms mo Ht Hh Hinv Hsf. apply (impl_must_exit t _ ms mo Ht); try assumption.
    eapply leaves_unreachable_impl_m; exact Ht.
  Qed.
End Halts.

(* [comment removed for export] *)
Section HaltsEqv.
  Variable segs : list Segment.
  Variable cfg : SpuriousCfg.
  Variable S : list word.
  Lemma must_exit_eqv : forall c, must_exit_in_at_cfg cfg segs S c ->
    forall c', cfg_eqv c c' -> must_exit_in_at_cfg cfg segs S c'.
  Proof.
    intros c H. induction H as [c code Hh Hin Hk | c Hh Hprog Hnerr Hnext IH]; intros c' Heqv.
    - pose proof Heqv as [_ Hmo]. apply must_exit_in_at_cfg_halted with (code := code); rewrite <- ?Hmo; assumption.
    - destruct c as [ms mo], c' as [ms' mo']. pose proof Heqv as [Hms Hmo]. cbn [cfg_ms cfg_model] in Hms, Hmo. subst mo'.
      apply must_exit_in_at_cfg_running.
      + exact Hh.
      + destruct Hprog as (evs & to & Hst).
        destruct (sstep_scfg_eqv segs cfg ms ms' mo evs to Hms Hst) as (X' & Hst' & _).
        exists evs, X'. exact Hst'.
      + intros evs Herr.
        destruct (sstep_scfg_eqv segs cfg ms' ms mo evs SError (ms_eqv_sym _ _ Hms) Herr) as (X & Hst & HX).
        destruct X as [c2|]; simpl in HX; [contradiction|].
        apply (Hnerr evs). exact Hst.
      + intros evs c2' Hst'.
        destruct (sstep_scfg_eqv segs cfg ms' ms mo evs (SNext c2') (ms_eqv_sym _ _ Hms) Hst') as (X & Hst & HX).
        destruct X as [c2|]; simpl in HX; [|contradiction].
        apply (IH evs c2). { exact Hst. } apply cfg_eqv_sym. exact HX.
  Qed.
End HaltsEqv.

Arguments impl_must_exit {node} segs cfg at_node nstep nexit minv nsafe NS S Hcodes {R} t Q ms mo.
Arguments impl_must_exit_lu {node} segs cfg at_node nstep nexit minv nsafe NS S Hcodes {R} t ms mo.
