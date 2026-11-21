(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the budget walk through the vDSO entry arms (the call, its materialization fault and its unmodeled case) under an invariant kept by with_vdso_bump). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition syscall_lt (Inv : Model -> Prop) (L : Z) : Prop :=
  forall (i : SyscallInput) (m : Model),
    Inv m ->
    L <= mlim m ->
    alloc_budget_refused_b i (sl L m) = false ->
    (forall eff mL' evs,
       syscall_spec i (sl L m) (Ok eff mL' evs) ->
       exists m', syscall_spec i m (Ok eff m' evs) /\ mL' = sl L m' /\ mlim m' = mlim m)
    /\ (forall eff m' evs,
          syscall_spec i m (Ok eff m' evs) ->
          syscall_spec i (sl L m) (Ok eff (sl L m') evs) /\ mlim m' = mlim m)
    /\ (syscall_spec i (sl L m) Unmodeled <-> syscall_spec i m Unmodeled).

(* [comment removed for export] *)
Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m _.
  destruct (classic (exists eff' m' evs',
                       syscall_spec i m (Ok eff' m' evs')
                       /\ refusal_b i m (eff_ret eff') = false)) as [Hex | Hno].
  - left. exact Hex.
  - right. intros eff' m' evs' Hspec.
    destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity |].
    exfalso. apply Hno. exists eff', m', evs'. split; [exact Hspec | exact E].
Qed.

Section Step.
Variable segs : list Segment.
Variable L : Z.
Variable Inv : Model -> Prop.
Hypothesis ARM : syscall_lt Inv L.
Hypothesis INV_SYS : forall i m eff m' evs, syscall_spec i m (Ok eff m' evs) -> Inv m -> Inv m'.
Hypothesis INV_MAT : forall m acc m', materialize_model_accesses m acc = Some m' -> Inv m -> Inv m'.
Hypothesis INV_VDSO : forall m, Inv m -> Inv (with_vdso_bump m).

Local Notation brf := (budget_refused_at segs).

(* [comment removed for export] *)
Lemma not_refused_alloc : forall ms m x8,
  m_halted m = None -> ms_svc_pending ms = Some x8 ->
  ~ brf (mkCfg ms m) ->
  alloc_budget_refused_b (sys_input segs ms x8) m = false.
Proof.
  intros ms m x8 Hh Hsvc Hn.
  destruct (alloc_budget_refused_b (sys_input segs ms x8) m) eqn:E; [| reflexivity].
  exfalso. apply Hn. split; [exact Hh |]. right. exists x8. split; [exact Hsvc |]. left. exact E.
Qed.

Lemma not_refused_effect : forall ms m x8 eff m' evs,
  m_halted m = None -> ms_svc_pending ms = Some x8 ->
  ~ brf (mkCfg ms m) ->
  syscall_spec (sys_input segs ms x8) m (Ok eff m' evs) -> m_halted m' = None ->
  materialize_model_accesses m' (syscall_effect_accesses eff) <> None.
Proof.
  intros ms m x8 eff m' evs Hh Hsvc Hn Hspec Hh' Hmat.
  apply Hn. split; [exact Hh |]. right. exists x8. split; [exact Hsvc |]. right.
  exists eff, m', evs. auto.
Qed.

Lemma not_refused_instr : forall ms m report,
  m_halted m = None -> ms_svc_pending ms = None ->
  ~ brf (mkCfg ms m) ->
  RiscvSemantics.step_accesses segs ms = MachineOk report ->
  materialize_model_accesses m (@accessed_ranges _ report) <> None.
Proof.
  intros ms m report Hh Hsvc Hn Hstep Hmat.
  apply Hn. split; [exact Hh |]. left. split; [exact Hsvc |]. left. exists report. auto.
Qed.

Lemma not_refused_vdso : forall ms m fn n eff m' evs,
  m_halted m = None -> ms_svc_pending ms = None ->
  ~ brf (mkCfg ms m) ->
  mi_account_step segs ms m = MachineUnmodeled ->
  vdso_entry_fn segs (ms_pc ms) = Some fn ->
  vdso_fn_sysno fn = Some n ->
  syscall_spec (sys_input segs ms (Z_to_bv 64 n)) m (Ok eff m' evs) ->
  eff_ret eff <> errno_ret EFAULT ->
  m_halted m' = None ->
  materialize_model_accesses m' (syscall_effect_accesses eff) <> None.
Proof.
  intros ms m fn n eff m' evs Hh Hsvc Hn Hacc Hfn Hno Hspec Hef Hh' Hmat.
  apply Hn. split; [exact Hh |]. left. split; [exact Hsvc |]. right.
  split; [exact Hacc |].
  exists fn, n, eff, m', evs.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma vdso_alloc_false : forall ms m fn n,
  Vdso.vdso_fn_sysno fn = Some n ->
  alloc_budget_refused_b (sys_input segs ms (Z_to_bv 64 n)) m = false.
Proof.
  intros ms m fn n H. destruct fn; cbn in H; try discriminate H;
    injection H as <-; reflexivity.
Qed.

Lemma acc_unmod_sl : forall ms m,
  mi_account_step segs ms (sl L m) = MachineUnmodeled <->
  mi_account_step segs ms m = MachineUnmodeled.
Proof.
  intros ms m. unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [r | |].
  - split; intro H;
      [ destruct (materialize_model_accesses (sl L m) (@accessed_ranges _ r))
      | destruct (materialize_model_accesses m (@accessed_ranges _ r)) ];
      discriminate H.
  - split; intro H; discriminate H.
  - split; intro H; reflexivity.
Qed.

Lemma vdso_unmod_sl_fwd : forall ms m fn,
  Inv m -> L <= mlim m ->
  vdso_call_unmodeled segs ms (sl L m) fn -> vdso_call_unmodeled segs ms m fn.
Proof.
  intros ms m fn HF HL Hun. unfold vdso_call_unmodeled in Hun |- *.
  destruct Hun as [H | [(n & Hn & Hs) | (n & eff & mL & evs & Hn & Hs & Hx)]].
  - left. exact H.
  - right. left. exists n. split; [exact Hn |].
    destruct (ARM _ m HF HL (vdso_alloc_false ms (sl L m) fn n Hn)) as (_ & _ & A3).
    exact (proj1 A3 Hs).
  - right. right.
    destruct (ARM _ m HF HL (vdso_alloc_false ms (sl L m) fn n Hn)) as (A1 & _ & _).
    destruct (A1 _ _ _ Hs) as (m' & Hs' & -> & _).
    exists n, eff, m', evs. split; [exact Hn |]. split; [exact Hs' | exact Hx].
Qed.

Lemma vdso_unmod_sl_bwd : forall ms m fn,
  Inv m -> L <= mlim m ->
  vdso_call_unmodeled segs ms m fn -> vdso_call_unmodeled segs ms (sl L m) fn.
Proof.
  intros ms m fn HF HL Hun. unfold vdso_call_unmodeled in Hun |- *.
  destruct Hun as [H | [(n & Hn & Hs) | (n & eff & m' & evs & Hn & Hs & Hx)]].
  - left. exact H.
  - right. left. exists n. split; [exact Hn |].
    destruct (ARM _ m HF HL (vdso_alloc_false ms (sl L m) fn n Hn)) as (_ & _ & A3).
    exact (proj2 A3 Hs).
  - right. right.
    destruct (ARM _ m HF HL (vdso_alloc_false ms (sl L m) fn n Hn)) as (_ & A2 & _).
    destruct (A2 _ _ _ Hs) as [HsL _].
    exists n, eff, (sl L m'), evs. split; [exact Hn |]. split; [exact HsL | exact Hx].
Qed.

(* [comment removed for export] *)
Lemma not_spurious_sl : forall cfg i m eff,
  Inv m -> L <= mlim m -> alloc_budget_refused_b i (sl L m) = false ->
  ~ spurious_refusal_cfg cfg i (sl L m) eff ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff HF HL Hb Hns (Hoff & Hr & eff' & m1 & evs1 & Hspec & Hnr).
  apply Hns. split; [exact Hoff |]. split; [exact Hr |].
  destruct (ARM i m HF HL Hb) as (_ & A2 & _).
  exists eff', (sl L m1), evs1. split; [exact (proj1 (A2 _ _ _ Hspec)) | exact Hnr].
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_sl_fwd : forall cfg c e X,
  Inv (cfg_model c) ->
  L <= mlim (cfg_model c) ->
  ~ brf (slc L c) ->
  sstep_cfg segs cfg (slc L c) e X ->
  exists X', sstep_cfg segs cfg c e X' /\ X = slst L X'
             /\ (forall c', X' = SNext c' ->
                   mlim (cfg_model c') = mlim (cfg_model c) /\ Inv (cfg_model c')).
Proof.
  intros cfg [ms m] e X HF HL Hn Hss. unfold slc in *. cbn [cfg_ms cfg_model] in *.
  inversion Hss; subst; clear Hss.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step _ _ _ = _ |- _ => rename H into Hacc end.
    unfold mi_account_step in Hacc.
    destruct (RiscvSemantics.step_accesses segs ms) as [report | |] eqn:Hstep; try discriminate.
    destruct (materialize_model_accesses (sl L m) (@accessed_ranges _ report)) as [mL'' |] eqn:Hmat;
      [| discriminate].
    injection Hacc as <- <-.
    destruct (materialize_sl_fwd L m _ _ HL Hmat) as (m'' & Hmat' & -> & Hlim).
    exists (SNext (mkCfg (@access_value _ report) m'')). split; [| split].
    + apply sstep_cfg_instr; [assumption | assumption |].
      unfold mi_account_step. rewrite Hstep, Hmat'. reflexivity.
    + reflexivity.
    + intros c' E. injection E as <-. split; [exact Hlim | exact (INV_MAT _ _ _ Hmat' HF)].
  - (* [comment removed for export] *)
    match goal with H : mi_account_step _ _ _ = _ |- _ => rename H into Hacc end.
    unfold mi_account_step in Hacc.
    destruct (RiscvSemantics.step_accesses segs ms) as [report | |] eqn:Hstep; try discriminate.
    + destruct (materialize_model_accesses (sl L m) (@accessed_ranges _ report)) as [mL'' |] eqn:Hmat;
        [discriminate |].
      exfalso. exact (not_refused_instr ms (sl L m) report ltac:(assumption) ltac:(assumption) Hn Hstep Hmat).
    + exists SError. split; [| split; [reflexivity | intros c' E; discriminate E]].
      apply sstep_cfg_instr_fault; [assumption | assumption |].
      unfold mi_account_step. rewrite Hstep. reflexivity.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step _ _ _ = _ |- _ => rename H into Hacc end.
    unfold mi_account_step in Hacc.
    destruct (RiscvSemantics.step_accesses segs ms) as [report | |] eqn:Hstep; try discriminate.
    + destruct (materialize_model_accesses (sl L m) (@accessed_ranges _ report)); discriminate.
    + exists SError. split; [| split; [reflexivity | intros c' E; discriminate E]].
      apply sstep_cfg_instr_unmodeled; [assumption | assumption | | assumption].
      unfold mi_account_step. rewrite Hstep. reflexivity.
  - (* vdso_call *)
    match goal with
    | Hacc : mi_account_step segs ms (sl L m) = MachineUnmodeled,
      Hfn : vdso_entry_fn segs (ms_pc ms) = Some ?fn,
      Hno : vdso_fn_sysno ?fn = Some ?n,
      Hspec : syscall_spec _ _ (Ok ?ef ?mL ?ev),
      Hmat : materialize_model_accesses _ _ = Some ?mL2,
      Hh : m_halted (sl L m) = None, Hh' : m_halted ?mL = None,
      Hef : eff_ret ?ef <> _, Hsvc : ms_svc_pending ms = None |- _ =>
        pose proof (vdso_alloc_false ms (sl L m) fn n Hno) as Hb;
        destruct (ARM _ m HF HL Hb) as (A1 & _ & _);
        destruct (A1 _ _ _ Hspec) as (m' & Hspec' & E1 & Hlim');
        subst mL;
        assert (HL' : L <= mlim m') by (rewrite Hlim'; exact HL);
        destruct (materialize_sl_fwd L m' _ _ HL' Hmat) as (m'' & Hmat' & E2 & Hlim'');
        subst mL2;
        eexists; split;
        [ eapply sstep_cfg_vdso_call;
          [ exact Hh | exact Hsvc | apply acc_unmod_sl; exact Hacc | exact Hfn | exact Hno
          | exact Hspec' | exact Hef | exact Hh' | exact Hmat' ]
        | split;
          [ reflexivity
          | intros c' E; injection E as <-; cbn [cfg_model]; split;
            [ change (mlim m'' = mlim m); rewrite Hlim''; exact Hlim'
            | apply INV_VDSO; exact (INV_MAT _ _ _ Hmat' (INV_SYS _ _ _ _ _ Hspec' HF)) ] ] ]
    end.
  - (* vdso_materialization_fault *)
    exfalso.
    match goal with
    | Hacc : mi_account_step segs ms (sl L m) = MachineUnmodeled,
      Hfn : vdso_entry_fn segs (ms_pc ms) = Some ?fn,
      Hno : vdso_fn_sysno ?fn = Some ?n,
      Hspec : syscall_spec _ _ (Ok ?ef ?mL ?ev),
      Hmat : materialize_model_accesses _ _ = None,
      Hh : m_halted (sl L m) = None, Hh' : m_halted ?mL = None,
      Hef : eff_ret ?ef <> _, Hsvc : ms_svc_pending ms = None |- _ =>
        exact (not_refused_vdso ms (sl L m) fn n ef mL ev Hh Hsvc Hn Hacc Hfn Hno Hspec Hef Hh' Hmat)
    end.
  - (* vdso_unmodeled *)
    exists SError. split; [| split; [reflexivity | intros c' E; discriminate E]].
    eapply sstep_cfg_vdso_unmodeled;
      [ assumption | assumption | apply acc_unmod_sl; assumption | eassumption
      | apply vdso_unmod_sl_fwd; [exact HF | exact HL | eassumption] ].
  - (* [comment removed for export] *)
    match goal with
    | Hsvc : ms_svc_pending ms = Some ?x, Hspec : syscall_spec _ _ (Ok ?ef ?mL ?ev),
      Hmat : materialize_model_accesses _ _ = Some ?mL2, Hns : ~ spurious_refusal_cfg _ _ _ _,
      Hh : m_halted (sl L m) = None, Hh' : m_halted ?mL = None |- _ =>
        pose proof (not_refused_alloc ms (sl L m) x Hh Hsvc Hn) as Hb;
        destruct (ARM _ m HF HL Hb) as (A1 & _ & _);
        destruct (A1 _ _ _ Hspec) as (m' & Hspec' & E1 & Hlim');
        subst mL;
        assert (HL' : L <= mlim m') by (rewrite Hlim'; exact HL);
        destruct (materialize_sl_fwd L m' _ _ HL' Hmat) as (m'' & Hmat' & E2 & Hlim'');
        subst mL2;
        exists (SNext (mkCfg (advance_past_svc (apply_effect ms ef)) m'')); split; [| split];
        [ exact (sstep_cfg_syscall segs cfg ms m x ef m' m'' ev Hh Hsvc Hspec'
                   (not_spurious_sl cfg _ m ef HF HL Hb Hns) Hh' Hmat')
        | reflexivity
        | intros c' E; injection E as <-; cbn [cfg_model]; split;
          [ rewrite Hlim''; exact Hlim'
          | exact (INV_MAT _ _ _ Hmat' (INV_SYS _ _ _ _ _ Hspec' HF)) ] ]
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | Hsvc : ms_svc_pending ms = Some ?x, Hspec : syscall_spec _ _ (Ok ?ef ?mL ?ev),
      Hmat : materialize_model_accesses _ _ = None,
      Hh : m_halted (sl L m) = None, Hh' : m_halted ?mL = None |- _ =>
        exact (not_refused_effect ms (sl L m) x ef mL ev Hh Hsvc Hn Hspec Hh' Hmat)
    end.
  - (* [comment removed for export] *)
    match goal with
    | Hsvc : ms_svc_pending ms = Some ?x, Hspec : syscall_spec _ _ (Ok ?ef ?mL ?ev),
      Hh : m_halted (sl L m) = None, Hh' : m_halted ?mL = Some ?code, Hk : m_killed ?mL = None |- _ =>
        pose proof (not_refused_alloc ms (sl L m) x Hh Hsvc Hn) as Hb;
        destruct (ARM _ m HF HL Hb) as (A1 & _ & _);
        destruct (A1 _ _ _ Hspec) as (m' & Hspec' & E1 & Hlim');
        subst mL;
        exists (SNext (mkCfg ms m')); split; [| split];
        [ exact (sstep_cfg_exit segs cfg ms m x ef m' ev code Hh Hsvc Hspec' Hh' Hk)
        | reflexivity
        | intros c' E; injection E as <-; split; [exact Hlim' | exact (INV_SYS _ _ _ _ _ Hspec' HF)] ]
    end.
  - (* [comment removed for export] *)
    match goal with
    | Hsvc : ms_svc_pending ms = Some ?x, Hspec : syscall_spec _ _ (Ok ?ef ?mL ?ev),
      Hh : m_halted (sl L m) = None, Hk : m_killed ?mL = Some ?sig |- _ =>
        pose proof (not_refused_alloc ms (sl L m) x Hh Hsvc Hn) as Hb;
        destruct (ARM _ m HF HL Hb) as (A1 & _ & _);
        destruct (A1 _ _ _ Hspec) as (m' & Hspec' & E1 & Hlim');
        subst mL;
        exists (SNext (mkCfg ms m')); split; [| split];
        [ exact (sstep_cfg_killed segs cfg ms m x ef m' ev sig Hh Hsvc Hspec' Hk)
        | reflexivity
        | intros c' E; injection E as <-; split; [exact Hlim' | exact (INV_SYS _ _ _ _ _ Hspec' HF)] ]
    end.
  - (* [comment removed for export] *)
    match goal with
    | Hsvc : ms_svc_pending ms = Some ?x, Hspec : syscall_spec _ _ Unmodeled,
      Hh : m_halted (sl L m) = None |- _ =>
        pose proof (not_refused_alloc ms (sl L m) x Hh Hsvc Hn) as Hb;
        destruct (ARM _ m HF HL Hb) as (_ & _ & A3);
        exists SError; split; [| split; [reflexivity | intros c' E; discriminate E]];
        exact (sstep_cfg_syscall_unmodeled segs cfg ms m x Hh Hsvc (proj1 A3 Hspec))
    end.
Qed.

(* [comment removed for export] *)
Lemma sstep_sl_progress : forall c e X,
  Inv (cfg_model c) ->
  L <= mlim (cfg_model c) ->
  ~ brf (slc L c) ->
  sstep segs c e X ->
  exists e' X', sstep segs (slc L c) e' X'.
Proof.
  intros [ms m] e X HF HL Hn Hss. unfold slc in *. cbn [cfg_ms cfg_model] in *.
  assert (INSTR : m_halted m = None -> ms_svc_pending ms = None ->
                  (mi_account_step segs ms m = MachineUnmodeled -> vdso_entry_fn segs (ms_pc ms) = None) ->
                  exists e' X', sstep segs (mkCfg ms (sl L m)) e' X').
  { intros Hh Hsvc Hnv.
    destruct (mi_account_step segs ms (sl L m)) as [[ms' m'] | |] eqn:E.
    - exists [], (SNext (mkCfg ms' m')). apply sstep_instr; assumption.
    - exists [], SError. apply sstep_instr_fault; assumption.
    - exists [], SError. apply sstep_instr_unmodeled; try assumption.
      apply Hnv. apply acc_unmod_sl. exact E. }
  (* The vDSO entry arms (08b1429): the call's outcome on [m] moves to [sl L m] by [ARM]. *)
  assert (VDSO : forall fn, m_halted m = None -> ms_svc_pending ms = None ->
                  mi_account_step segs ms m = MachineUnmodeled ->
                  vdso_entry_fn segs (ms_pc ms) = Some fn ->
                  (vdso_call_unmodeled segs ms m fn \/
                   exists n eff m' evs, vdso_fn_sysno fn = Some n /\
                     syscall_spec (sys_input segs ms (Z_to_bv 64 n)) m (Ok eff m' evs) /\
                     eff_ret eff <> errno_ret EFAULT /\ m_halted m' = None) ->
                  exists e' X', sstep segs (mkCfg ms (sl L m)) e' X').
  { intros fn Hh Hsvc Hacc Hfn Hc.
    assert (HaccL : mi_account_step segs ms (sl L m) = MachineUnmodeled)
      by (apply acc_unmod_sl; exact Hacc).
    assert (HhL : m_halted (sl L m) = None) by exact Hh.
    destruct Hc as [Hu | (n & eff & m' & evs & Hno & Hspec & Hef & Hh')].
    - exists [], SError. eapply sstep_vdso_unmodeled; try eassumption.
      destruct Hu as [Hu | [(n & Hno & Hspec) | (n & eff & m' & evs & Hno & Hspec & Hor)]].
      + left; exact Hu.
      + right; left. exists n. split; [exact Hno |].
        destruct (ARM _ m HF HL (vdso_alloc_false ms (sl L m) fn n Hno)) as (_ & _ & A3).
        apply A3; exact Hspec.
      + right; right.
        destruct (ARM _ m HF HL (vdso_alloc_false ms (sl L m) fn n Hno)) as (_ & A2 & _).
        destruct (A2 _ _ _ Hspec) as [HspecL _].
        exists n, eff, (sl L m'), evs. split; [exact Hno |]. split; [exact HspecL |]. exact Hor.
    - destruct (ARM _ m HF HL (vdso_alloc_false ms (sl L m) fn n Hno)) as (_ & A2 & _).
      destruct (A2 _ _ _ Hspec) as [HspecL _].
      assert (HhL' : m_halted (sl L m') = None) by exact Hh'.
      destruct (materialize_model_accesses (sl L m') (syscall_effect_accesses eff)) as [m'' |] eqn:Hmat.
      + eexists _, _. eapply sstep_vdso_call; eassumption.
      + eexists _, _. eapply sstep_vdso_materialization_fault; eassumption. }
  assert (SYS : forall x8 eff m' evs, m_halted m = None -> ms_svc_pending ms = Some x8 ->
                  syscall_spec (sys_input segs ms x8) m (Ok eff m' evs) ->
                  exists e' X', sstep segs (mkCfg ms (sl L m)) e' X').
  { intros x8 eff m' evs Hh Hsvc Hspec.
    pose proof (not_refused_alloc ms (sl L m) x8 Hh Hsvc Hn) as Hb.
    destruct (ARM _ m HF HL Hb) as (_ & A2 & _).
    destruct (A2 _ _ _ Hspec) as [HspecL _].
    destruct (m_killed (sl L m')) as [sig |] eqn:Hk.
    { eexists _, _. eapply sstep_killed; eassumption. }
    destruct (m_halted (sl L m')) as [code |] eqn:Hh'.
    { eexists _, _. eapply sstep_exit; eassumption. }
    destruct (materialize_model_accesses (sl L m') (syscall_effect_accesses eff)) as [m'' |] eqn:Hmat.
    { eexists _, _. eapply sstep_syscall; eassumption. }
    { eexists _, _. eapply sstep_syscall_materialization_fault; eassumption. } }
  inversion Hss; subst; clear Hss;
    try (apply INSTR; [assumption | assumption | intros HU; first [congruence | assumption]]);
    try (eapply SYS; eassumption);
    try (eapply VDSO; [eassumption .. | left; eassumption]);
    try (eapply VDSO; [eassumption .. | right; do 4 eexists; repeat split; eassumption]).
  (* [comment removed for export] *)
  match goal with
  | Hsvc : ms_svc_pending ms = Some ?x, Hspec : syscall_spec _ _ Unmodeled |- _ =>
      pose proof (not_refused_alloc ms (sl L m) x ltac:(assumption) Hsvc Hn) as Hb;
      destruct (ARM _ m HF HL Hb) as (_ & _ & A3);
      exists [], SError; eapply sstep_syscall_unmodeled; [eassumption | eassumption | apply A3; exact Hspec]
  end.
Qed.

(* [comment removed for export] *)
Theorem must_exit_in_at_cfg_sl : forall cfg S c,
  must_exit_in_at_cfg cfg segs S c ->
  Inv (cfg_model c) ->
  L <= mlim (cfg_model c) ->
  ~ reaches_budget_refused_cfg segs cfg (slc L c) ->
  must_exit_in_at_cfg cfg segs S (slc L c).
Proof.
  intros cfg S c H.
  induction H as [c code Hh Hin Hk | c Hnone (e0 & X0 & Hss0) Hnoerr Hnext IH]; intros HF HL Hnbr.
  - apply (must_exit_in_at_cfg_halted cfg segs S (slc L c) code); [exact Hh | exact Hin | exact Hk].
  - assert (Hn : ~ brf (slc L c)).
    { intros Hb. apply Hnbr. exists [], (slc L c). split; [apply star_cfg_refl | exact Hb]. }
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + destruct (sstep_sl_progress c e0 X0 HF HL Hn (sstep_cfg_sub segs cfg _ _ _ Hss0)) as (e' & X' & Hss').
      destruct c as [ms m].
      apply (sstep_cfg_progress segs cfg ms (sl L m) e' X'); [| exact Hss'].
      intros x8 _. apply refusal_decided_classic.
    + intros e Herr.
      destruct (sstep_cfg_sl_fwd cfg c e SError HF HL Hn Herr) as (X' & Hss' & HX & _).
      destruct X' as [c' |]; [discriminate HX |]. exact (Hnoerr e Hss').
    + intros e cL' Hss.
      destruct (sstep_cfg_sl_fwd cfg c e (SNext cL') HF HL Hn Hss) as (X' & Hss' & HX & Hlim).
      destruct X' as [c' |]; [| discriminate HX]. cbn in HX. injection HX as ->.
      destruct (Hlim c' eq_refl) as [Hl' Hf'].
      apply (IH e c' Hss').
      * exact Hf'.
      * rewrite Hl'. exact HL.
      * intros (tr & c2 & Hstar & Hb). apply Hnbr.
        exists (e ++ tr), c2. split; [| exact Hb].
        eapply star_cfg_step; [exact Hss | exact Hstar].
Qed.

End Step.
