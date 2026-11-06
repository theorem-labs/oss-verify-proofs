(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import ShapeAlg SpinAlg. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import ShapeEFS Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.

(* [comment removed for export] *)
Definition ev_nokill (e : event) : Prop :=
  match e with KillEv _ _ => False | _ => True end.

(* [comment removed for export] *)
Definition nokill (T : TSet) : Prop := forall tr, T tr -> Forall ev_nokill tr.

Lemma is_prefix_Forall {A} (P : A -> Prop) : forall (a l : list A),
  is_prefix a l -> Forall P l -> Forall P a.
Proof.
  induction a as [|x a IH]; intros l Hp Hl; [constructor|].
  destruct l as [|y l]; [cbn in Hp; contradiction|].
  cbn in Hp. destruct Hp as [-> Hp]. inversion Hl; subst.
  constructor; [assumption | eapply IH; eauto].
Qed.

Lemma nokill_nil : nokill t_nil.
Proof. intros tr H. unfold t_nil in H. subst tr. constructor. Qed.

Lemma nokill_emit : forall evs T, Forall ev_nokill evs -> nokill T -> nokill (t_emit evs T).
Proof.
  intros evs T He HT tr [Hp | (tr' & -> & Htr')].
  - eapply is_prefix_Forall; eauto.
  - apply Forall_app. split; [exact He | exact (HT _ Htr')].
Qed.

Lemma nokill_alt2 : forall A B, nokill A -> nokill B -> nokill (t_alt2 A B).
Proof. intros A B HA HB tr [H|H]; [apply HA | apply HB]; exact H. Qed.

Lemma nokill_exit : forall code fs, nokill (t_exit code fs).
Proof.
  intros code fs. unfold t_exit. apply nokill_emit; [| apply nokill_nil].
  constructor; [exact I | constructor].
Qed.

Lemma nokill_t_eq : forall T T', t_eq T T' -> nokill T -> nokill T'.
Proof. intros T T' Heq HT tr H. apply HT. apply (proj2 (Heq tr)). exact H. Qed.

(* [comment removed for export] *)
Lemma W_nokill : forall ch s, Forall ev_nokill (W ch s).
Proof. intros ch s. unfold W. induction s as [|b s IH]; cbn; constructor; [exact I | exact IH]. Qed.

Lemma nokill_die : forall msg fs, nokill (t_die msg fs).
Proof. intros msg fs. unfold t_die. apply nokill_emit; [apply W_nokill | apply nokill_exit]. Qed.

Lemma nokill_body : forall data fs, nokill (t_body data fs).
Proof.
  intros data fs. unfold t_body. cbv zeta.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply nokill_die|].
  destruct (length data <? HDR_MIN)%nat; [apply nokill_die|].
  destruct (length data <? HDR_MIN + config_len data)%nat; [apply nokill_die|].
  apply nokill_emit; [apply W_nokill | apply nokill_exit].
Qed.

Theorem spec_nokill : forall argv fs, nokill (spec argv fs).
Proof.
  intros argv fs. unfold spec.
  destruct argv as [|a0 [|path [|x l]]]; try apply nokill_die.
  destruct (4096 <=? length path)%nat; [apply nokill_die|].
  destruct (list_byte_eqb path []); [apply nokill_die|].
  destruct (list_byte_eqb path dot_path).
  - apply nokill_alt2; [apply nokill_die | unfold t_opened_dir; apply nokill_die].
  - destruct (fs_lookup fs path) as [data|].
    + apply nokill_alt2; [apply nokill_die | unfold t_opened; apply nokill_body].
    + apply nokill_die.
Qed.

(* [comment removed for export] *)
Theorem shape_strong_equiv_ss_unkilled :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  nokill T ->
  srealizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free_unkilled (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free_unkilled (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp HT Hsource Htarget.
  destruct (shape_strong_equiv_ss source_segs rpc rph rsp rbrk rmb rrnd rlim
              target_segs apc aph asp abrk amb arnd alim T inp Hsource Htarget) as (Es & Et & Etr).
  assert (K : forall segs c, srealizes segs c T ->
             ~ (exists tr sig fs, obs_trace_cfg segs ACFG c tr /\ In (KillEv sig fs) tr)).
  { intros segs c Hc (tr & sig & fs & Hobs & Hin).
    apply (srealizes_obs_iff segs c T Hc tr) in Hobs.
    pose proof (HT tr Hobs) as HF. rewrite Forall_forall in HF. exact (HF _ Hin). }
  split; [| split].
  - split; [exact Es | cbn; apply K; exact Hsource].
  - split; [exact Et | cbn; apply K; exact Htarget].
  - exact Etr.
Qed.
