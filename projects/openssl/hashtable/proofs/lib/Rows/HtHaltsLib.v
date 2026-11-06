(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ShapeAlg Spec SpecGen HTSpec.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg HaltsCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition codes02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma in_codes02_0 : In (exit_code 0) codes02.  Proof. left. reflexivity. Qed.
Lemma in_codes02_2 : In (exit_code 2) codes02.  Proof. right. left. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma exits_in_W_exit : forall S ch msg code fs,
  In code S -> exits_in S (t_emit (W ch msg) (t_exit code fs)).
Proof.
  intros S ch msg code fs Hin. apply exits_in_emit.
  - unfold W. apply Forall_exits_in_writes.
  - apply exits_in_exit. exact Hin.
Qed.

Lemma exits_in_t_die : forall S msg fs, In (exit_code 2) S -> exits_in S (t_die msg fs).
Proof. intros S msg fs Hin. unfold t_die. apply exits_in_W_exit. exact Hin. Qed.

Lemma exits_in_t_body_pre : forall S data fs, In (exit_code 2) S -> exits_in S (t_body_pre data fs).
Proof.
  intros S data fs Hin. unfold t_body_pre.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply exits_in_t_die; exact Hin|].
  destruct (length data <? HDR_MIN)%nat; apply exits_in_t_die; exact Hin.
Qed.

Lemma exits_in_t_opened_dir : forall S path fs, In (exit_code 2) S -> exits_in S (t_opened_dir path fs).
Proof. intros S path fs Hin. unfold t_opened_dir. apply exits_in_t_die. exact Hin. Qed.

Lemma exits_in_t_body_g : forall S (KT : list byte -> Fs.Fs -> TSet) data fs,
  In (exit_code 2) S -> exits_in S (KT data fs) -> exits_in S (t_body_g KT data fs).
Proof.
  intros S KT data fs Hin HKT. unfold t_body_g.
  destruct (body_pre_target data); [apply exits_in_t_body_pre; exact Hin | exact HKT].
Qed.

(* [comment removed for export] *)
Lemma exits_in_spec_g : forall S (KT : list byte -> Fs.Fs -> TSet),
  In (exit_code 2) S -> (forall data fs, exits_in S (KT data fs)) ->
  forall argv fs, exits_in S (spec_g KT argv fs).
Proof.
  intros S KT Hin HKT argv fs. unfold spec_g.
  destruct (drv_classify argv fs) as [| path | path | path data].
  - apply exits_in_t_die. exact Hin.
  - apply exits_in_t_die. exact Hin.
  - apply exits_in_alt2; [apply exits_in_t_die | apply exits_in_t_opened_dir]; exact Hin.
  - apply exits_in_alt2; [apply exits_in_t_die; exact Hin | apply exits_in_t_body_g; [exact Hin | apply HKT]].
Qed.

(* [comment removed for export] *)
Lemma exits_in_t_target_ht : forall S data fs,
  In (exit_code (ht_status data)) S -> exits_in S (t_target_ht data fs).
Proof. intros S data fs Hin. unfold t_target_ht. apply exits_in_W_exit. exact Hin. Qed.

(* [comment removed for export] *)
Lemma ht_status_in_codes02 : forall data, In (exit_code (ht_status data)) codes02.
Proof.
  intros data. unfold ht_status.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  first [exact in_codes02_0 | exact in_codes02_2].
Qed.

Lemma exits_in_t_target_ht_02 : forall data fs, exits_in codes02 (t_target_ht data fs).
Proof. intros data fs. apply exits_in_t_target_ht. apply ht_status_in_codes02. Qed.

(* [comment removed for export] *)
Lemma exits_in_cannot_or : forall S path (T : TSet) fs,
  In (exit_code 2) S -> exits_in S T -> exits_in S (t_alt2 (t_die (msg_cannot_open path) fs) T).
Proof. intros S path T fs Hin HT. apply exits_in_alt2; [apply exits_in_t_die; exact Hin | exact HT]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition full_stmt (cfg : SpuriousCfg) (img : Image) (lim : Z) (KT : list byte -> Fs.Fs -> TSet) : Prop :=
  forall sp brk mbase rnd (inp : ProcInput),
    valid_sp sp -> valid_brk (img_segments img) brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_input inp ->
    realizes_cfg cfg (img_segments img)
      (init_config (img_segments img) (img_init_pc img) (img_phdrs img) sp brk mbase rnd lim inp)
      (spec_g KT (in_argv inp) (in_fs inp)).

(* [comment removed for export] *)
Lemma full_stmt_init_cfg : forall cfg img lim KT en inp,
  full_stmt cfg img lim KT -> valid_entry img en inp -> valid_input inp ->
  realizes_cfg cfg (img_segments img) (init_cfg img lim en inp) (spec_g KT (in_argv inp) (in_fs inp)).
Proof.
  intros cfg [segs pc ph] lim KT [sp brk mbase rnd] inp HF Hen Hv.
  pose proof (valid_input_va_size _ Hv) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as (Hsp & Hbrk & Hmb & Hfit).
  cbn [init_cfg]. exact (HF sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hv).
Qed.

(* [comment removed for export] *)
Theorem halts_of_full : forall cfg img lim KT (S : list word),
  In (exit_code 2) S ->
  (forall data fs, exits_in S (KT data fs)) ->
  full_stmt cfg img lim KT ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S img.
Proof.
  intros cfg img lim KT S Hin HKT HF.
  apply (halts_of_realizes_cfg_nopremise cfg). intros en inp Hen Hv.
  exists (spec_g KT (in_argv inp) (in_fs inp)). split.
  - exact (full_stmt_init_cfg cfg img lim KT en inp HF Hen Hv).
  - apply exits_in_spec_g; [exact Hin | exact HKT].
Qed.

