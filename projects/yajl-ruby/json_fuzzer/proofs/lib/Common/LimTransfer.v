(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase LimStep LimInv LimSyscall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem must_exit_in_at_cfg_limit : forall segs cfg S L c,
  must_exit_in_at_cfg cfg segs S c ->
  linv (cfg_model c) ->
  L <= mlim (cfg_model c) ->
  ~ reaches_budget_refused_cfg segs cfg (slc L c) ->
  must_exit_in_at_cfg cfg segs S (slc L c).
Proof.
  intros segs cfg S L c.
  exact (must_exit_in_at_cfg_sl segs L linv (syscall_lt_all L) linv_sys linv_mat cfg S c).
Qed.

(* [comment removed for export] *)
Lemma init_config_slc : forall segs pc ph sp brk0 mbase rnd lb ls inp,
  slc ls (init_config segs pc ph sp brk0 mbase rnd lb inp)
  = init_config segs pc ph sp brk0 mbase rnd ls inp.
Proof. reflexivity. Qed.

Lemma init_config_mlim : forall segs pc ph sp brk0 mbase rnd lim inp,
  mlim (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp)) = lim.
Proof. reflexivity. Qed.

Lemma init_config_linv : forall segs pc ph sp brk0 mbase rnd lim inp,
  linv (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp)).
Proof. intros. apply linv_init. Qed.

Theorem must_exit_in_scfg_limit : forall cfg S img lb ls en inp,
  ls <= lb ->
  must_exit_in_scfg cfg S img lb en inp ->
  source_within_budget_scfg cfg ls img en inp ->
  must_exit_in_scfg cfg S img ls en inp.
Proof.
  intros cfg S [segs pc ph] lb ls [sp brk0 mbase rnd] inp Hle Hbig Hprem.
  cbn [must_exit_in_scfg] in *.
  unfold source_within_budget_scfg, run_scfg_budget_refused in Hprem.
  rewrite <- (init_config_slc segs pc ph sp brk0 mbase rnd lb ls inp).
  apply must_exit_in_at_cfg_limit.
  - exact Hbig.
  - apply init_config_linv.
  - rewrite init_config_mlim. exact Hle.
  - rewrite init_config_slc. exact Hprem.
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_budgets_of_big : forall cfg S img lb ls,
  ls <= lb ->
  (forall en inp, valid_entry img en inp -> valid_input inp ->
                  must_exit_in_scfg cfg S img lb en inp) ->
  halts_allowed_T_scfg_budgets cfg ls S img.
Proof.
  intros cfg S img lb ls Hle Hbig en inp HE HI Hprem.
  exact (must_exit_in_scfg_limit cfg S img lb ls en inp Hle (Hbig en inp HE HI) Hprem).
Qed.
