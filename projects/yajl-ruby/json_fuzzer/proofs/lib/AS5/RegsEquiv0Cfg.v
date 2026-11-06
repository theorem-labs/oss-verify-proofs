(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import RegsEquiv0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma sstep_scfg_eqv_ms : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
  exists X', sstep_cfg segs cfg (mkCfg ms' mo) evs X' /\ to_eqv X X'.
Proof.
  intros ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv segs ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hms <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_cfg_instr; auto; congruence|]. split; [exact Hms| reflexivity].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
  - match goal with H : mi_account_step segs ms mo = _ |- _ => rewrite H in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_unmodeled; auto; congruence| exact I].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_cfg_syscall segs cfg ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption
        | rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  - (* [comment removed for export] *)
    exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_materialization_fault segs cfg ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption
      | rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption| assumption| assumption].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_exit segs cfg ms' mo x8 eff model' evs0 code);
        [assumption| congruence| rewrite <- (sys_input_eqv segs ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - (* [comment removed for export] *)
    exists (SNext (mkCfg ms' model')). split.
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
  apply (sstep_scfg_eqv_ms ms ms'); assumption.
Qed.

Lemma star_scfg_eqv : forall c tr c1, star_cfg segs cfg c tr c1 ->
  forall c', cfg_eqv c c' -> exists c1', star_cfg segs cfg c' tr c1' /\ cfg_eqv c1 c1'.
Proof.
  intros c tr c1 H. induction H as [c | c evs c2 tr c3 Hst Hstar IH]; intros c' Heqv.
  - exists c'. split; [apply star_cfg_refl| exact Heqv].
  - destruct (sstep_scfg_eqv c c' evs (SNext c2) Heqv Hst) as (X' & Hst' & HX).
    destruct X' as [c2'|]; simpl in HX; [|contradiction].
    destruct (IH c2' HX) as (c3' & Hstar' & H3).
    exists c3'. split; [eapply star_cfg_step; eassumption| exact H3].
Qed.

Lemma obs_trace_scfg_eqv : forall c c' tr, cfg_eqv c c' ->
  obs_trace_cfg segs cfg c tr -> obs_trace_cfg segs cfg c' tr.
Proof.
  intros c c' tr Heqv (tr' & c1 & Hstar & Hp).
  destruct (star_scfg_eqv c tr' c1 Hstar c' Heqv) as (c1' & Hstar' & _).
  exists tr', c1'. split; assumption.
Qed.

Lemma reaches_error_scfg_eqv : forall c c', cfg_eqv c c' ->
  reaches_error_cfg segs cfg c -> reaches_error_cfg segs cfg c'.
Proof.
  intros c c' Heqv (tr & c1 & evs & Hstar & Hst).
  destruct (star_scfg_eqv c tr c1 Hstar c' Heqv) as (c1' & Hstar' & H1).
  destruct (sstep_scfg_eqv c1 c1' evs SError H1 Hst) as (X' & Hst' & HX).
  destruct X'; simpl in HX; [contradiction|].
  exists tr, c1', evs. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma behaves_cfg_eqv : forall c c' T, cfg_eqv c c' ->
  behaves_cfg cfg segs c T -> behaves_cfg cfg segs c' T.
Proof.
  intros c c' T Heqv [Hobs Herr]. pose proof (cfg_eqv_sym _ _ Heqv) as Heqv'. split.
  - intros tr. split; intros H.
    + apply Hobs. exact (obs_trace_scfg_eqv _ _ tr Heqv' H).
    + exact (obs_trace_scfg_eqv _ _ tr Heqv (proj2 (Hobs tr) H)).
  - intros H. apply Herr. exact (reaches_error_scfg_eqv _ _ Heqv' H).
Qed.


(* [comment removed for export] *)
Lemma realizes_cfg_eqv : forall c T, realizes_cfg cfg segs c T -> forall c', cfg_eqv c c' -> realizes_cfg cfg segs c' T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 [Hcomp Hsound] Hnx IH | c Hh | c T T' H IH Heq]; intros c' Heqv.
  - (* [comment removed for export] *)
    set (J := { p : I * config | sstep_cfg segs cfg c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
    assert (Hex : forall i, exists c2, sstep_cfg segs cfg c' (evs i) (SNext c2) /\ cfg_eqv (nx i) c2).
    { intros i. destruct (sstep_scfg_eqv c c' (evs i) (SNext (nx i)) Heqv (Hcomp i)) as (X' & Hst' & HX).
      destruct X' as [c2|]; simpl in HX; [|contradiction]. exists c2. split; assumption. }
    destruct (Hex i0) as (c20 & H20 & E20).
    set (j0 := (exist _ (i0, c20) (conj H20 E20)) : J).
    apply (rz_conseq_cfg cfg segs c' (t_alt (fun j : J => t_emit (evs (fst (proj1_sig j))) (T (fst (proj1_sig j)))))).
    + apply (rz_node_cfg cfg segs c' J (fun j => evs (fst (proj1_sig j))) (fun j => snd (proj1_sig j)) (fun j => T (fst (proj1_sig j))) j0).
      * split.
        -- intros [[i c2] [Hs He]]. exact Hs.
        -- intros e st Hst.
           destruct (sstep_scfg_eqv c' c e st (cfg_eqv_sym _ _ Heqv) Hst) as (X & HstX & HX).
           destruct (Hsound e X HstX) as (i & -> & ->).
           destruct st as [c2|]; simpl in HX; [|contradiction].
           exists (exist _ (i, c2) (conj Hst (cfg_eqv_sym _ _ HX))). split; reflexivity.
      * intros [[i c2] [Hs He]]. cbn [fst snd proj1_sig]. exact (IH i c2 He).
    + (* [comment removed for export] *)
      intros tr. unfold t_alt. split.
      * intros [[[i c2] [Hs He]] Htr]. cbn [fst proj1_sig] in Htr. exists i. exact Htr.
      * intros [i Htr]. destruct (Hex i) as (c2 & Hs & He). exists (exist _ (i, c2) (conj Hs He)). exact Htr.
  - apply rz_halt_cfg. destruct Heqv as [_ <-]. exact Hh.
  - eapply rz_conseq_cfg; [exact (IH c' Heqv) | exact Heq].
Qed.


End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition canonR (R : bvmap 5 word) : bvmap 5 word :=
  mkR (reg_get R 1%bv) (reg_get R 2%bv) (reg_get R 3%bv) (reg_get R 4%bv) (reg_get R 5%bv) (reg_get R 6%bv) (reg_get R 7%bv)
      (reg_get R 8%bv) (reg_get R 9%bv) (reg_get R 10%bv) (reg_get R 11%bv) (reg_get R 12%bv) (reg_get R 13%bv) (reg_get R 14%bv)
      (reg_get R 15%bv) (reg_get R 16%bv) (reg_get R 17%bv) (reg_get R 18%bv) (reg_get R 19%bv) (reg_get R 20%bv) (reg_get R 21%bv)
      (reg_get R 22%bv) (reg_get R 23%bv) (reg_get R 24%bv) (reg_get R 25%bv) (reg_get R 26%bv) (reg_get R 27%bv) (reg_get R 28%bv)
      (reg_get R 29%bv) (reg_get R 30%bv) (reg_get R 31%bv).

Lemma reg_of_nat0 : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range _ r) as H. change (bv_modulus 5) with 32%Z in H.
  split; [| lia]. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32%Z.
  rewrite Z2Nat.id, Z.mod_small by lia; lia.
Qed.

Lemma canonR_eqv0 : forall R, regs_eqv0 (canonR R) R.
Proof.
  intros R r Hr. destruct (reg_of_nat0 r) as (n & -> & Hn).
  destruct n as [|n]; [exfalso; apply Hr; apply bv_eq; reflexivity|].
  do 31 (destruct n as [|n]; [reflexivity|]). lia.
Qed.
