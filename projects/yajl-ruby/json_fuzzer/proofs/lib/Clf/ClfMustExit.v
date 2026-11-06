(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree RunCeiling Nodes RegsEquiv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_fam_on (cfg : SpuriousCfg) (n : node) : Prop :=
  forall segs ms x8, at_node segs n ms -> ms_svc_pending ms = Some x8 ->
    injected_family_off cfg (sys_input segs ms x8) = false.

Lemma injected_family_off_sysno : forall cfg segs ms (no : Z),
  injected_arm (bv_unsigned (Z_to_bv 64 no)) = None ->
  injected_family_off cfg (sys_input segs ms (Z_to_bv 64 no)) = false.
Proof.
  intros cfg segs ms no H. unfold injected_family_off. rewrite in_sysno_si, H. reflexivity.
Qed.

Lemma node_fam_on_set_tid : forall cfg, node_fam_on cfg NSetTid.
Proof.
  intros cfg segs ms x8 Hat Hsvc. cbn [at_node] in Hat. rewrite Hat in Hsvc. injection Hsvc as <-.
  apply injected_family_off_sysno. vm_compute. reflexivity.
Qed.

Lemma node_fam_on_exit : forall cfg c, node_fam_on cfg (NExit c).
Proof.
  intros cfg c segs ms x8 Hat Hsvc. cbn [at_node] in Hat. destruct Hat as [[H|H] _];
    rewrite H in Hsvc; injection Hsvc as <-; apply injected_family_off_sysno; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint exits_with_cfg (cfg : SpuriousCfg) (code : word) {R : Type} (t : itree node R) (mo : Model) {struct t} : Prop :=
  match t with
  | Ret _ => False
  | Vis n k =>
      nsafe n mo
      /\ node_fam_on cfg n
      /\ match n with
         | NExit c => code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)
         | _ => True
         end
      /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> exits_with_cfg cfg code (k rsp) mo'
  end.

Section WithSegs.
  Context {RC__ : RunCeiling}.   (* [comment removed for export] *)
  Variable segs : list Segment.
  Variable cfg : SpuriousCfg.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma mstep_must_exit_cfg : forall code ms ms1 mo,
    m_halted mo = None -> m_vm_lazy mo = [] ->
    mstep segs ms ms1 ->
    must_exit_at_cfg cfg segs code (mkCfg ms1 mo) ->
    must_exit_at_cfg cfg segs code (mkCfg ms mo).
  Proof.
    intros code ms ms1 mo Hh Hlz Hm Hk.
    apply must_exit_at_cfg_running.
    - exact Hh.
    - apply (sstep_cfg_progress segs cfg ms mo [] (SNext (mkCfg ms1 mo))).
      + intros x8 Hsvc. exfalso. pose proof (mstep_not_svc segs ms ms1 Hm). congruence.
      + apply (mstep_sstep segs); assumption.
    - intros evs Hss. apply sstep_cfg_sub in Hss.
      destruct (sstep_mstep_inv segs ms mo ms1 evs SError Hlz Hm Hss) as [_ E]. discriminate E.
    - intros evs c' Hss. apply sstep_cfg_sub in Hss.
      destruct (sstep_mstep_inv segs ms mo ms1 evs (SNext c') Hlz Hm Hss) as [_ E].
      injection E as ->. exact Hk.
  Qed.

  Lemma msteps_must_exit_cfg : forall code ms ms' mo,
    m_halted mo = None -> m_vm_lazy mo = [] ->
    msteps segs ms ms' ->
    must_exit_at_cfg cfg segs code (mkCfg ms' mo) ->
    must_exit_at_cfg cfg segs code (mkCfg ms mo).
  Proof.
    intros code ms ms' mo Hh Hlz Hm. induction Hm as [ms | ms ms1 ms2 H1 H2 IH]; intros Hk.
    - exact Hk.
    - eapply mstep_must_exit_cfg; [exact Hh | exact Hlz | exact H1 | exact (IH Hk)].
  Qed.

  Lemma evt_must_exit_cfg : forall code (Q : machine_state -> Prop) ms mo,
    m_halted mo = None -> m_vm_lazy mo = [] ->
    evt segs Q ms ->
    (forall ms', Q ms' -> must_exit_at_cfg cfg segs code (mkCfg ms' mo)) ->
    must_exit_at_cfg cfg segs code (mkCfg ms mo).
  Proof.
    intros code Q ms mo Hh Hlz (ms' & Hm & HQ) HK.
    eapply msteps_must_exit_cfg; [exact Hh | exact Hlz | exact Hm | exact (HK ms' HQ)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Let NS := nodes_sound segs.

  Lemma node_must_exit_cfg : forall code n ms mo,
    at_node segs n ms -> m_halted mo = None -> minv mo -> nsafe n mo -> node_fam_on cfg n ->
    match n with NExit c => code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) | _ => True end ->
    (forall rsp mo' evs, nstep n mo rsp mo' evs -> m_halted mo' = None -> minv mo' ->
       must_exit_at_cfg cfg segs code (mkCfg (nret ms rsp) mo')) ->
    must_exit_at_cfg cfg segs code (mkCfg ms mo).
  Proof.
    intros code n ms mo Hat Hh Hinv Hsf Hfam Hcode HK.
    apply must_exit_at_cfg_running.
    - exact Hh.
    - assert (Hprog : exists evs st, sstep segs (mkCfg ms mo) evs st).
      { destruct (ns_progress _ _ _ _ _ _ _ NS n ms mo Hat Hh Hinv Hsf) as [(rsp & mo' & evs & Hst) | (c & mo' & Hex)].
        + destruct (ns_sound _ _ _ _ _ _ _ NS n ms mo rsp mo' evs Hat Hh Hinv Hsf Hst) as (_ & _ & Hss). eauto.
        + destruct (ns_exit _ _ _ _ _ _ _ NS n ms mo c mo' Hat Hh Hinv Hsf Hex) as (_ & Hss). eauto. }
      destruct Hprog as (evs & st & Hss).
      apply (sstep_cfg_progress segs cfg ms mo evs st); [| exact Hss].
      intros x8 Hsvc Hoff. rewrite (Hfam segs ms x8 Hat Hsvc) in Hoff. discriminate Hoff.
    - intros evs Hss. apply sstep_cfg_sub in Hss.
      destruct (ns_complete _ _ _ _ _ _ _ NS n ms mo evs SError Hat Hh Hinv Hsf Hss)
        as [(rsp & mo' & E & _) | (c & mo' & E & _)]; discriminate E.
    - intros evs c' Hss. apply sstep_cfg_sub in Hss.
      destruct (ns_complete _ _ _ _ _ _ _ NS n ms mo evs (SNext c') Hat Hh Hinv Hsf Hss)
        as [(rsp & mo' & E & Hst) | (c & mo' & E & Hex & _)].
      + injection E as ->.
        destruct (ns_sound _ _ _ _ _ _ _ NS n ms mo rsp mo' evs Hat Hh Hinv Hsf Hst) as (Hh' & Hinv' & _).
        exact (HK rsp mo' evs Hst Hh' Hinv').
      + injection E as ->. apply must_exit_at_cfg_halted; cbn [cfg_model].
        * destruct n; try (exact (False_ind _ Hex)).
          destruct Hex as [-> ->]. cbn in Hcode. subst code. apply m_halted_with_halted.
        * destruct n; try (exact (False_ind _ Hex)).
          destruct Hex as [-> ->]. apply m_killed_with_halted.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem impl_must_exit_cfg : forall code {R : Type} (t : itree node R) (Q : R -> machine_state -> Prop) ms mo,
    impl segs (at_node segs) t Q ms ->
    exits_with_cfg cfg code t mo ->
    m_halted mo = None -> minv mo ->
    must_exit_at_cfg cfg segs code (mkCfg ms mo).
  Proof.
    intros code R t. induction t as [r | n k IH]; intros Q ms mo Himpl Hex Hh Hinv.
    - exact (False_ind _ Hex).
    - cbn in Himpl. destruct Hex as (Hsf & Hfam & Hcode & Hk).
      pose proof (minv_lazy _ Hinv) as Hlz.
      eapply evt_must_exit_cfg; [exact Hh | exact Hlz | exact Himpl |].
      intros ms1 [Hat Himpl1].
      eapply (node_must_exit_cfg code n ms1 mo); try assumption.
      intros rsp mo' evs Hst Hh' Hinv'.
      eapply (IH rsp Q); [exact (Himpl1 rsp) | exact (Hk rsp mo' evs Hst) | exact Hh' | exact Hinv'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sstep_scfg_ms_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
    sstep_cfg segs cfg (mkCfg ms mo) evs X ->
    exists X', sstep_cfg segs cfg (mkCfg ms' mo) evs X' /\ to_eqv X X'.
  Proof.
    intros ms ms' mo evs X Heqv Hst.
    pose proof (mi_account_step_eqv segs ms ms' mo Heqv) as Hres.
    pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
    inversion Hst; subst.
    - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
      destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
      destruct Hres as [Hms <-].
      exists (SNext (mkCfg ms1' model')). split; [apply sstep_cfg_instr; auto; congruence|]. split; [exact Hms| reflexivity].
    - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
      destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
      exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
    - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
      destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
      exists SError. split; [apply sstep_cfg_instr_unmodeled; auto; congruence| exact I].
    - exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
      + apply (sstep_cfg_syscall segs cfg ms' mo x8 eff model' model'' evs);
          [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption
          | rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption | assumption| assumption].
      + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
    - exists SError. split; [|exact I].
      apply (sstep_cfg_syscall_materialization_fault segs cfg ms' mo x8 eff model' evs0);
        [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption
        | rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption | assumption| assumption].
    - exists (SNext (mkCfg ms' model')). split.
      + apply (sstep_cfg_exit segs cfg ms' mo x8 eff model' evs0 code);
          [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption| assumption| assumption].
      + split; [exact Heqv| reflexivity].
    - exists (SNext (mkCfg ms' model')). split.
      + apply (sstep_cfg_killed segs cfg ms' mo x8 eff model' evs0 sig);
          [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption| assumption].
      + split; [exact Heqv| reflexivity].
    - exists SError. split; [|exact I].
      apply (sstep_cfg_syscall_unmodeled segs cfg ms' mo x8);
        [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption].
  Qed.

  Lemma sstep_scfg_eqv : forall c c' evs X, cfg_eqv c c' ->
    sstep_cfg segs cfg c evs X -> exists X', sstep_cfg segs cfg c' evs X' /\ to_eqv X X'.
  Proof.
    intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
    apply (sstep_scfg_ms_eqv ms ms'); assumption.
  Qed.

  Lemma must_exit_at_cfg_eqv : forall code c, must_exit_at_cfg cfg segs code c ->
    forall c', cfg_eqv c c' -> must_exit_at_cfg cfg segs code c'.
  Proof.
    intros code c H. induction H as [c Hh Hk | c Hnone Hprog Hnoerr Hnext IH]; intros c' Heqv.
    - apply must_exit_at_cfg_halted; destruct Heqv as [_ Hmo]; rewrite <- Hmo; assumption.
    - apply must_exit_at_cfg_running.
      + destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hnone.
      + destruct Hprog as (evs & st & Hss).
        destruct (sstep_scfg_eqv c c' evs st Heqv Hss) as (X' & Hss' & _). eauto.
      + intros evs Hss'.
        destruct (sstep_scfg_eqv c' c evs SError (cfg_eqv_sym _ _ Heqv) Hss') as (X & Hss & HX).
        destruct X as [c2|]; cbn in HX; [contradiction|]. exact (Hnoerr evs Hss).
      + intros evs c2' Hss'.
        destruct (sstep_scfg_eqv c' c evs (SNext c2') (cfg_eqv_sym _ _ Heqv) Hss') as (X & Hss & HX).
        destruct X as [c2|]; cbn in HX; [|contradiction].
        apply (IH evs c2 Hss). apply cfg_eqv_sym. exact HX.
  Qed.
End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem must_exit_with_scfg_of_impl : forall {RC__ : RunCeiling} cfg code segs pc ph lim en inp {R : Type} (t : itree node R) Q,
  bv_unsigned (en_sp en) = rc_sp -> valid_sp (en_sp en) ->
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  exits_with_cfg cfg code t (mo0 segs lim en inp) ->
  must_exit_with_scfg cfg code (mkImage segs pc ph) lim en inp.
Proof.
  intros RC__ cfg code segs pc ph lim [sp brk mb dr] inp R t Q Hrc Hv Himpl Hex.
  cbn [must_exit_with_scfg].
  change (init_config segs pc ph sp brk mb dr lim inp)
    with (init_config segs pc ph (en_sp (mkEntry sp brk mb dr)) (en_brk (mkEntry sp brk mb dr))
                      (en_mmap_base (mkEntry sp brk mb dr)) (en_draw (mkEntry sp brk mb dr)) lim inp).
  rewrite init_config_eq.
  apply (must_exit_at_cfg_eqv segs cfg code (mkCfg (ms0 segs pc ph (mkEntry sp brk mb dr) inp) (mo0 segs lim (mkEntry sp brk mb dr) inp))).
  - eapply impl_must_exit_cfg; [exact Himpl | exact Hex | apply mo0_not_halted | apply mo0_minv; assumption].
  - split; [| reflexivity]. cbn [cfg_ms]. apply ms_eqv_sym. apply init_machine_state_eqv.
Qed.
