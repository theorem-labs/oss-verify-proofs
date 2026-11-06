(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimRun.v at commit 874e3397a35, with its module paths changed to libpcap/fuzz_pcap. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs RiscvSemantics MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lim Require Import LimBase LimMm LimSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cfgL (L : Z) (c : config) : config := mkCfg (cfg_ms c) (setL L (cfg_model c)).

(* [comment removed for export] *)
Definition down216 (L : Z) (i : SyscallInput) (m : Model) : Prop :=
  alloc_budget_refused_b i (setL L m) = false ->
  (exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false) ->
  (exists eff m' evs, syscall_spec i (setL L m) (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma materialize_up : forall L m acc m', (mlim m <= L)%Z ->
  materialize_model_accesses m acc = Some m' ->
  materialize_model_accesses (setL L m) acc = Some (setL L m') /\ mlim m' = mlim m.
Proof.
  intros L m acc m' HL H. unfold materialize_model_accesses in *.
  change (m_vm_lazy (setL L m)) with (m_vm_lazy m).
  change (m_vm_materialized (setL L m)) with (m_vm_materialized m).
  change (vm_backing_used (setL L m)) with (vm_backing_used m).
  change (vm_limit (m_vmmaps (setL L m))) with L.
  unfold materialize_accesses in *. cbv zeta in *.
  destruct (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) acc) as [|p ps].
  - injection H as <-. split; reflexivity.
  - destruct (vm_backing_used m + Z.of_nat (length (p :: ps)) * page_size <=? vm_limit (m_vmmaps m))%Z eqn:E; [| discriminate H].
    injection H as <-.
    assert (E2 : (vm_backing_used m + Z.of_nat (length (p :: ps)) * page_size <=? L)%Z = true).
    { apply Z.leb_le. apply Z.leb_le in E. unfold mlim in HL. lia. }
    rewrite E2. split; reflexivity.
Qed.

Lemma setL_back : forall L m, setL (mlim m) (setL L m) = m.
Proof. intros. rewrite setL_setL. apply setL_id. Qed.

(* [comment removed for export] *)
Lemma materialize_big : forall L mb acc ms', (L <= mlim mb)%Z ->
  materialize_model_accesses (setL L mb) acc = Some ms' ->
  exists mb', materialize_model_accesses mb acc = Some mb' /\ ms' = setL L mb' /\ mlim mb' = mlim mb.
Proof.
  intros L mb acc ms' HL H.
  destruct (materialize_up (mlim mb) (setL L mb) acc ms') as [Ha Hb]; [rewrite mlim_setL; exact HL | exact H |].
  rewrite setL_back in Ha. rewrite mlim_setL in Hb.
  exists (setL (mlim mb) ms'). split; [exact Ha|]. split; [| reflexivity].
  rewrite setL_setL. symmetry. apply setL_eq_of_mlim. exact Hb.
Qed.

Lemma syscall_spec_big : forall L i mb eff ms' evs, (L <= mlim mb)%Z ->
  alloc_budget_refused_b i (setL L mb) = false ->
  syscall_spec i (setL L mb) (Ok eff ms' evs) ->
  exists mb', syscall_spec i mb (Ok eff mb' evs) /\ ms' = setL L mb' /\ mlim mb' = mlim mb.
Proof.
  intros L i mb eff ms' evs HL R H.
  destruct (syscall_spec_up (mlim mb) i (setL L mb) _ ltac:(rewrite mlim_setL; exact HL) R H) as [Ha Hb].
  cbn [omap opres] in Ha, Hb. rewrite setL_back in Ha. rewrite mlim_setL in Hb.
  exists (setL (mlim mb) ms'). split; [exact Ha|]. split; [| reflexivity].
  rewrite setL_setL. symmetry. apply setL_eq_of_mlim. exact Hb.
Qed.

Lemma syscall_spec_big_unmodeled : forall L i mb, (L <= mlim mb)%Z ->
  alloc_budget_refused_b i (setL L mb) = false ->
  syscall_spec i (setL L mb) Unmodeled -> syscall_spec i mb Unmodeled.
Proof.
  intros L i mb HL R H.
  destruct (syscall_spec_up (mlim mb) i (setL L mb) _ ltac:(rewrite mlim_setL; exact HL) R H) as [Ha _].
  cbn [omap] in Ha. rewrite setL_back in Ha. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma spurious_down : forall cfg L i mb eff, (L <= mlim mb)%Z ->
  alloc_budget_refused_b i (setL L mb) = false ->
  (bv_unsigned (in_sysno i) = 216%Z -> down216 L i mb) ->
  spurious_refusal_cfg cfg i mb eff -> spurious_refusal_cfg cfg i (setL L mb) eff.
Proof.
  intros cfg L i mb eff HL R H216 (Hoff & Hr & Hex).
  split; [exact Hoff|]. split; [exact Hr|].
  destruct (Z.eq_dec (bv_unsigned (in_sysno i)) 216) as [E|E].
  - exact (H216 E R Hex).
  - destruct Hex as (eff' & m' & evs' & Hs & Hnr).
    destruct (syscall_spec_down L i mb _ HL R E Hs) as [Ha _]. cbn [omap] in Ha.
    exists eff', (setL L m'), evs'. split; [exact Ha | exact Hnr].
Qed.

(* [comment removed for export] *)
Section Run.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma not_refused_mark : forall ms m x8,
  m_halted m = None -> ms_svc_pending ms = Some x8 ->
  ~ budget_refused_at segs (mkCfg ms m) ->
  alloc_budget_refused_b (sys_input segs ms x8) m = false.
Proof.
  intros ms m x8 Hh Hsvc Hnb.
  destruct (alloc_budget_refused_b (sys_input segs ms x8) m) eqn:E; [| reflexivity].
  exfalso. apply Hnb. split; [exact Hh|]. right. exists x8. split; [exact Hsvc|]. left. exact E.
Qed.

(* [comment removed for export] *)
Lemma step_up : forall L ms mb evs c',
  (L <= mlim mb)%Z ->
  ~ budget_refused_at segs (mkCfg ms (setL L mb)) ->
  (forall x8, ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 216%Z -> down216 L (sys_input segs ms x8) mb) ->
  sstep_cfg segs cfg (mkCfg ms (setL L mb)) evs (SNext c') ->
  exists cb', sstep_cfg segs cfg (mkCfg ms mb) evs (SNext cb') /\ c' = cfgL L cb' /\ mlim (cfg_model cb') = mlim mb.
Proof.
  intros L ms mb evs c' HL Hnb H216 Hss.
  inversion Hss as
    [ ms0 m0 ms1 m1 Hh Hsvc Hacc
    | | | ms0 m0 x8 eff m1 m2 evs0 Hh Hsvc Hs Hns Hh1 Hmat
    | | ms0 m0 x8 eff m1 evs0 code Hh Hsvc Hs Hh1 Hk1
    | ms0 m0 x8 eff m1 evs0 sig Hh Hsvc Hs Hk1 | ]; subst.
  - (* [comment removed for export] *)
    unfold mi_account_step in Hacc.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; try discriminate Hacc.
    destruct (materialize_model_accesses (setL L mb) (@accessed_ranges _ report)) as [m'|] eqn:Em; [| discriminate Hacc].
    injection Hacc as <- <-.
    destruct (materialize_big L mb _ _ HL Em) as (mb' & Hb & -> & Hl).
    exists (mkCfg (@access_value _ report) mb'). split; [| split; [reflexivity | exact Hl]].
    apply sstep_cfg_instr; [exact Hh | exact Hsvc |].
    unfold mi_account_step. rewrite Est, Hb. reflexivity.
  - (* [comment removed for export] *)
    pose proof (not_refused_mark _ _ _ Hh Hsvc Hnb) as R.
    destruct (syscall_spec_big L _ mb _ _ _ HL R Hs) as (mb1 & Hsb & -> & Hl1).
    destruct (materialize_big L mb1 _ _ ltac:(rewrite Hl1; exact HL) Hmat) as (mb2 & Hmb & -> & Hl2).
    exists (mkCfg (advance_past_svc (apply_effect ms eff)) mb2). split; [| split; [reflexivity | cbn [cfg_model]; rewrite Hl2; exact Hl1]].
    eapply sstep_cfg_syscall; [exact Hh | exact Hsvc | exact Hsb | | exact Hh1 | exact Hmb].
    intros Hsp. apply Hns. apply spurious_down; [exact HL | exact R | | exact Hsp].
    intros E. apply (H216 x8 Hsvc). exact E.
  - (* [comment removed for export] *)
    pose proof (not_refused_mark _ _ _ Hh Hsvc Hnb) as R.
    destruct (syscall_spec_big L _ mb _ _ _ HL R Hs) as (mb1 & Hsb & -> & Hl1).
    exists (mkCfg ms mb1). split; [| split; [reflexivity | exact Hl1]].
    exact (sstep_cfg_exit segs cfg ms mb x8 eff mb1 evs0 code Hh Hsvc Hsb Hh1 Hk1).
  - (* [comment removed for export] *)
    pose proof (not_refused_mark _ _ _ Hh Hsvc Hnb) as R.
    destruct (syscall_spec_big L _ mb _ _ _ HL R Hs) as (mb1 & Hsb & -> & Hl1).
    exists (mkCfg ms mb1). split; [| split; [reflexivity | exact Hl1]].
    exact (sstep_cfg_killed segs cfg ms mb x8 eff mb1 evs0 sig Hh Hsvc Hsb Hk1).
Qed.

(* [comment removed for export] *)
Lemma error_up : forall L ms mb evs,
  (L <= mlim mb)%Z ->
  ~ budget_refused_at segs (mkCfg ms (setL L mb)) ->
  sstep_cfg segs cfg (mkCfg ms (setL L mb)) evs SError ->
  exists evs', sstep_cfg segs cfg (mkCfg ms mb) evs' SError.
Proof.
  intros L ms mb evs HL Hnb Hss.
  inversion Hss as
    [ | ms0 m0 Hh Hsvc Hacc | ms0 m0 Hh Hsvc Hacc
    | | ms0 m0 x8 eff m1 evs0 Hh Hsvc Hs Hns Hh1 Hmat
    | | | ms0 m0 x8 Hh Hsvc Hs ]; subst.
  - (* [comment removed for export] *)
    unfold mi_account_step in Hacc.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; try discriminate Hacc.
    + destruct (materialize_model_accesses (setL L mb) (@accessed_ranges _ report)) as [m'|] eqn:Em; [discriminate Hacc|].
      exfalso. apply Hnb. split; [exact Hh|]. left. split; [exact Hsvc|]. exists report. split; [exact Est | exact Em].
    + exists []. apply sstep_cfg_instr_fault; [exact Hh | exact Hsvc |]. unfold mi_account_step. rewrite Est. reflexivity.
  - (* [comment removed for export] *)
    unfold mi_account_step in Hacc.
    destruct (step_accesses segs ms) as [report| |] eqn:Est; try discriminate Hacc.
    + destruct (materialize_model_accesses (setL L mb) (@accessed_ranges _ report)); discriminate Hacc.
    + exists []. apply sstep_cfg_instr_unmodeled; [exact Hh | exact Hsvc |]. unfold mi_account_step. rewrite Est. reflexivity.
  - (* [comment removed for export] *)
    exfalso. apply Hnb. split; [exact Hh|]. right. exists x8. split; [exact Hsvc|]. right.
    exists eff, m1, evs0. split; [exact Hs|]. split; [exact Hh1 | exact Hmat].
  - (* [comment removed for export] *)
    pose proof (not_refused_mark _ _ _ Hh Hsvc Hnb) as R.
    exists []. eapply sstep_cfg_syscall_unmodeled; [exact Hh | exact Hsvc |].
    exact (syscall_spec_big_unmodeled L _ mb HL R Hs).
Qed.

(* [comment removed for export] *)
Lemma sstep_of_outcome : forall ms m x8 o,
  m_halted m = None -> ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) m o ->
  exists evs st, sstep segs (mkCfg ms m) evs st.
Proof.
  intros ms m x8 [eff m1 evs|] Hh Hsvc Hs.
  - destruct (m_killed m1) as [sig|] eqn:Ek.
    { eexists _, _. eapply sstep_killed; eassumption. }
    destruct (m_halted m1) as [code|] eqn:Eh.
    { eexists _, _. eapply sstep_exit; eassumption. }
    destruct (materialize_model_accesses m1 (syscall_effect_accesses eff)) as [m2|] eqn:Em.
    + eexists _, _. eapply sstep_syscall; eassumption.
    + eexists _, _. eapply sstep_syscall_materialization_fault; eassumption.
  - eexists _, _. eapply sstep_syscall_unmodeled; eassumption.
Qed.

Lemma progress_down : forall L ms mb evs st,
  (L <= mlim mb)%Z ->
  ~ budget_refused_at segs (mkCfg ms (setL L mb)) ->
  sstep_cfg segs cfg (mkCfg ms mb) evs st ->
  exists evs' st', sstep_cfg segs cfg (mkCfg ms (setL L mb)) evs' st'.
Proof.
  intros L ms mb evs st HL Hnb Hss.
  assert (Hh : m_halted mb = None) by (inversion Hss; assumption).
  assert (Hu : exists evs' st', sstep segs (mkCfg ms (setL L mb)) evs' st').
  { destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
    - assert (Ho : exists o, syscall_spec (sys_input segs ms x8) mb o).
      { inversion Hss; subst; try congruence;
          match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in H; injection H as <- end;
          eexists; eassumption. }
      destruct Ho as [o Ho].
      pose proof (not_refused_mark ms (setL L mb) x8 Hh Hsvc Hnb) as R.
      assert (Hos : exists o', syscall_spec (sys_input segs ms x8) (setL L mb) o').
      { destruct (Z.eq_dec (bv_unsigned (in_sysno (sys_input segs ms x8))) 216) as [E|E].
        - apply syscall_spec_216_has_outcome. exact E.
        - destruct (syscall_spec_down L _ mb o HL R E Ho) as [Ha _]. eexists; exact Ha. }
      destruct Hos as [o' Ho'].
      exact (sstep_of_outcome ms (setL L mb) x8 o' Hh Hsvc Ho').
    - destruct (mi_account_step segs ms (setL L mb)) as [[ms' m']| |] eqn:Ea.
      + eexists _, _. eapply sstep_instr; eassumption.
      + eexists _, _. eapply sstep_instr_fault; eassumption.
      + eexists _, _. eapply sstep_instr_unmodeled; eassumption. }
  destruct Hu as (evs' & st' & Hu).
  apply (sstep_cfg_progress segs cfg ms (setL L mb) evs' st'); [| exact Hu].
  intros x8 _ _.
  destruct (classic (exists eff' m' evs0,
      syscall_spec (sys_input segs ms x8) (setL L mb) (Ok eff' m' evs0)
      /\ refusal_b (sys_input segs ms x8) (setL L mb) (eff_ret eff') = false)) as [H|H].
  - left. exact H.
  - right. intros eff' m' evs0 Hs.
    destruct (refusal_b (sys_input segs ms x8) (setL L mb) (eff_ret eff')) eqn:E; [reflexivity|].
    exfalso. apply H. exists eff', m', evs0. split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem lim_transfer_at : forall (S : list word) (L : Z) (Inv : config -> Prop),
  (forall c evs c', Inv c -> sstep_cfg segs cfg c evs (SNext c') -> Inv c') ->
  (forall ms m x8, Inv (mkCfg ms m) -> m_halted m = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 216%Z ->
     (L <= mlim m)%Z -> down216 L (sys_input segs ms x8) m) ->
  forall c, must_exit_in_at_cfg cfg segs S c ->
    Inv c -> (L <= mlim (cfg_model c))%Z ->
    ~ reaches_budget_refused_cfg segs cfg (cfgL L c) ->
    must_exit_in_at_cfg cfg segs S (cfgL L c).
Proof.
  intros S L Inv Hclosed H216 c H.
  induction H as [c code Hh Hin Hk | c Hnone Hex Hnoerr _ IH]; intros HI HL Hnr.
  - exact (must_exit_in_at_cfg_halted cfg segs S (cfgL L c) code Hh Hin Hk).
  - destruct c as [ms mb]. cbn [cfg_model cfg_ms cfgL] in *.
    assert (Hnb : ~ budget_refused_at segs (mkCfg ms (setL L mb))).
    { intros Hb. apply Hnr. exists [], (mkCfg ms (setL L mb)). split; [apply star_cfg_refl | exact Hb]. }
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + destruct Hex as (evs & st & Hss). exact (progress_down L ms mb evs st HL Hnb Hss).
    + intros evs Herr. destruct (error_up L ms mb evs HL Hnb Herr) as [evs' He]. exact (Hnoerr evs' He).
    + intros evs c' Hss.
      destruct (step_up L ms mb evs c' HL Hnb) as (cb' & Hsb & -> & Hl); [| exact Hss |].
      { intros x8 Hsvc E. exact (H216 ms mb x8 HI Hnone Hsvc E HL). }
      apply (IH evs cb' Hsb).
      * exact (Hclosed _ _ _ HI Hsb).
      * rewrite Hl. exact HL.
      * intros (tr & c2 & Hst & Hb). apply Hnr. exists (evs ++ tr), c2. split; [| exact Hb].
        eapply star_cfg_step; [exact Hss | exact Hst].
Qed.

End Run.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma init_config_cfgL : forall segs pc ph sp brk0 mbase rnd lim L inp,
  cfgL L (init_config segs pc ph sp brk0 mbase rnd lim inp) = init_config segs pc ph sp brk0 mbase rnd L inp.
Proof. reflexivity. Qed.
Lemma init_config_mlim : forall segs pc ph sp brk0 mbase rnd lim inp,
  mlim (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp)) = lim.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem lim_transfer : forall cfg segs S pc ph sp brk0 mbase rnd inp lim_small lim_big,
  (lim_small <= lim_big)%Z ->
  (forall tr ms m x8,
     star_cfg segs cfg (init_config segs pc ph sp brk0 mbase rnd lim_big inp) tr (mkCfg ms m) ->
     m_halted m = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 216%Z ->
     down216 lim_small (sys_input segs ms x8) m) ->
  must_exit_in_at_cfg cfg segs S (init_config segs pc ph sp brk0 mbase rnd lim_big inp) ->
  ~ reaches_budget_refused_cfg segs cfg (init_config segs pc ph sp brk0 mbase rnd lim_small inp) ->
  must_exit_in_at_cfg cfg segs S (init_config segs pc ph sp brk0 mbase rnd lim_small inp).
Proof.
  intros cfg segs S pc ph sp brk0 mbase rnd inp lim_small lim_big Hle H216 Hbig Hnr.
  rewrite <- (init_config_cfgL segs pc ph sp brk0 mbase rnd lim_big lim_small inp).
  apply (lim_transfer_at segs cfg S lim_small
           (fun c => exists tr, star_cfg segs cfg (init_config segs pc ph sp brk0 mbase rnd lim_big inp) tr c)).
  - intros c evs c' [tr Hst] Hss. exists (tr ++ evs).
    clear - Hst Hss. induction Hst as [c0 | c1 e c2 tr c3 Hs1 Hst IH].
    + rewrite <- (app_nil_r evs). cbn [app]. eapply star_cfg_step; [exact Hss | apply star_cfg_refl].
    + rewrite <- app_assoc. eapply star_cfg_step; [exact Hs1 | exact (IH Hss)].
  - intros ms m x8 [tr Hst] Hh Hsvc E _. exact (H216 tr ms m x8 Hst Hh Hsvc E).
  - exact Hbig.
  - exists []. apply star_cfg_refl.
  - rewrite init_config_mlim. exact Hle.
  - rewrite init_config_cfgL. exact Hnr.
Qed.

(* [comment removed for export] *)
Corollary lim_transfer_no_mremap : forall cfg segs S pc ph sp brk0 mbase rnd inp lim_small lim_big,
  (lim_small <= lim_big)%Z ->
  (forall tr c x8,
     star_cfg segs cfg (init_config segs pc ph sp brk0 mbase rnd lim_big inp) tr c ->
     m_halted (cfg_model c) = None -> ms_svc_pending (cfg_ms c) = Some x8 -> bv_unsigned x8 <> 216%Z) ->
  must_exit_in_at_cfg cfg segs S (init_config segs pc ph sp brk0 mbase rnd lim_big inp) ->
  ~ reaches_budget_refused_cfg segs cfg (init_config segs pc ph sp brk0 mbase rnd lim_small inp) ->
  must_exit_in_at_cfg cfg segs S (init_config segs pc ph sp brk0 mbase rnd lim_small inp).
Proof.
  intros cfg segs S pc ph sp brk0 mbase rnd inp lim_small lim_big Hle Hno Hbig Hnr.
  apply (lim_transfer cfg segs S pc ph sp brk0 mbase rnd inp lim_small lim_big Hle); [| exact Hbig | exact Hnr].
  intros tr ms m x8 Hst Hh Hsvc E. exfalso. exact (Hno tr (mkCfg ms m) x8 Hst Hh Hsvc E).
Qed.
