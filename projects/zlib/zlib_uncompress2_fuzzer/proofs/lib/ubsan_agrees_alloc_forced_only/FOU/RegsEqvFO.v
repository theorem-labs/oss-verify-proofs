(** * FOU.RegsEqvFO — register-equivalent configurations step alike under the filtered relation

    [Mr.MrRegsEqvW.sstep_eqv] / [sstep_cfg_eqv] over [Run.sstep_cfg]: two machine states that agree on
    every register but x0 (and on everything else) present the same syscall input, so an outcome that is
    not a spurious refusal in one is not one in the other. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Frame.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrRegsEqvW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma sstep_scfg_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
  exists X', sstep_cfg segs cfg (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv segs ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & Hpc0 & Hsvc & _ & _ & _ & _).  (* the pc equality, for the 727 arms *)
  pose proof (fun x8 => sys_input_eqv segs ms ms' x8 Heqv) as Hsi.
  inversion Hst; subst.
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hres Hmo].
    exists (SNext (mkCfg ms1' mo1')). split; [apply sstep_cfg_instr; auto; congruence|]. split; [exact Hres| exact Hmo].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_unmodeled; auto; unfold ms_pc in *; congruence| exact I].
  - (* the three vDSO arms of sstep_cfg, as Lib/RegsEquivFO *)
    match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    eexists. split.
    + apply (sstep_cfg_vdso_call segs cfg ms' mo fn n eff model' model'' evs);
        [assumption| congruence| exact E| unfold ms_pc in *; congruence| assumption
        | rewrite <- (Hsi _); assumption| assumption| assumption| assumption].
    + split; [apply vdso_post_eqv; exact Heqv| reflexivity].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    apply (sstep_cfg_vdso_materialization_fault segs cfg ms' mo fn n eff model' evs0);
      [assumption| congruence| exact E| unfold ms_pc in *; congruence| assumption
      | rewrite <- (Hsi _); assumption| assumption| assumption| assumption].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    apply (sstep_cfg_vdso_unmodeled segs cfg ms' mo fn); [assumption| congruence| exact E| unfold ms_pc in *; congruence|].
    match goal with Hu : vdso_call_unmodeled _ ms mo fn |- _ =>
      destruct Hu as [Hu0 | [(n0 & Hn & Hs) | (n0 & eff0 & mo0 & evs1 & Hn & Hs & Hr)]] end;
      [left; exact Hu0
      | right; left; exists n0; rewrite <- (Hsi _); split; assumption
      | right; right; exists n0, eff0, mo0, evs1; rewrite <- (Hsi _); repeat split; assumption].
  - match goal with
    | Hs : ms_svc_pending ms = Some ?x, Hsp : syscall_spec _ mo (Ok ?eff ?m1 ?ev),
      Hn : ~ spurious_refusal_cfg _ _ mo ?eff, Hh1 : m_halted ?m1 = None,
      Hmat : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
        exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) m2)); split;
        [ apply (sstep_cfg_syscall segs cfg ms' mo x eff m1 m2 ev);
          [ assumption | congruence | rewrite <- Hsi; exact Hsp | rewrite <- Hsi; exact Hn | exact Hh1 | exact Hmat ]
        | split; [apply advance_past_svc_eqv, apply_effect_eqv, Heqv | reflexivity] ]
    end.
  - match goal with
    | Hs : ms_svc_pending ms = Some ?x, Hsp : syscall_spec _ mo (Ok ?eff ?m1 ?ev),
      Hn : ~ spurious_refusal_cfg _ _ mo ?eff, Hh1 : m_halted ?m1 = None,
      Hmat : materialize_model_accesses ?m1 _ = None |- _ =>
        exists SError; split; [|exact I];
        apply (sstep_cfg_syscall_materialization_fault segs cfg ms' mo x eff m1 ev);
        [ assumption | congruence | rewrite <- Hsi; exact Hsp | rewrite <- Hsi; exact Hn | exact Hh1 | exact Hmat ]
    end.
  - match goal with
    | Hs : ms_svc_pending ms = Some ?x, Hsp : syscall_spec _ mo (Ok ?eff ?m1 ?ev),
      Hh1 : m_halted ?m1 = Some ?code, Hk : m_killed ?m1 = None |- _ =>
        exists (SNext (mkCfg ms' m1)); split;
        [ apply (sstep_cfg_exit segs cfg ms' mo x eff m1 ev code);
          [ assumption | congruence | rewrite <- Hsi; exact Hsp | exact Hh1 | exact Hk ]
        | split; [exact Heqv | reflexivity] ]
    end.
  - match goal with
    | Hs : ms_svc_pending ms = Some ?x, Hsp : syscall_spec _ mo (Ok ?eff ?m1 ?ev),
      Hk : m_killed ?m1 = Some ?sig |- _ =>
        exists (SNext (mkCfg ms' m1)); split;
        [ apply (sstep_cfg_killed segs cfg ms' mo x eff m1 ev sig);
          [ assumption | congruence | rewrite <- Hsi; exact Hsp | exact Hk ]
        | split; [exact Heqv | reflexivity] ]
    end.
  - match goal with
    | Hs : ms_svc_pending ms = Some ?x, Hsp : syscall_spec _ mo Unmodeled |- _ =>
        exists SError; split; [|exact I];
        apply (sstep_cfg_syscall_unmodeled segs cfg ms' mo x);
        [ assumption | congruence | rewrite <- Hsi; exact Hsp ]
    end.
Qed.

Lemma sstep_scfg_cfg_eqv : forall c c' evs X, cfg_eqv c c' ->
  sstep_cfg segs cfg c evs X -> exists X', sstep_cfg segs cfg c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_scfg_eqv ms ms'); assumption.
Qed.

End WithSegs.
