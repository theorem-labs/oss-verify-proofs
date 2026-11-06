From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK15.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Definition run_exact (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) (T : list event -> Prop) : Prop :=
  error_free (run_scfg ACFG img lim en inp) /\ forall tr, bh_traces (run_scfg ACFG img lim en inp) tr <-> T tr.
Definition rz_run (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) (T : TSet) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd => realizes segs (init_config segs pc ph sp brk0 mbase rnd lim inp) T
  end.
Definition cf_run (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd => cut_free segs (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.
Lemma cf_run_of_budget : forall img lim en inp,
  ~ run_scfg_budget_refused ACFG img lim en inp -> cf_run img lim en inp.
Proof. intros [segs pc ph] lim [sp brk0 mbase rnd] inp H. exact (cut_free_intro segs _ H). Qed.
Lemma budget_of_cf_run : forall img lim en inp,
  cf_run img lim en inp -> ~ run_scfg_budget_refused ACFG img lim en inp.
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp H (tr & c & Hstar & Hb). exact (H tr c Hstar Hb).
Qed.
Theorem run_exact_of_rz : forall img lim en inp T,
  rz_run img lim en inp T -> cf_run img lim en inp -> run_exact img lim en inp T.
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp T HR HC. split.
  - exact (realizes_no_error segs _ T HR HC).
  - exact (realizes_obs_iff segs _ T HR HC).
Qed.
Theorem agree_of_exact : forall img_p lim_p en_p img_s lim_s en_s inp (T_p T_s : list event -> Prop),
  run_exact img_p lim_p en_p inp T_p -> run_exact img_s lim_s en_s inp T_s ->
  (forall tr, T_p tr <-> T_s tr) ->
  error_free (run_scfg ACFG img_p lim_p en_p inp) /\ error_free (run_scfg ACFG img_s lim_s en_s inp) /\
  trace_equiv (bh_traces (run_scfg ACFG img_p lim_p en_p inp)) (bh_traces (run_scfg ACFG img_s lim_s en_s inp)).
Proof.
  intros img_p lim_p en_p img_s lim_s en_s inp T_p T_s [Hp Hpt] [Hs Hst] HT.
  split; [exact Hp|]. split; [exact Hs|]. intros tr. rewrite Hpt, Hst. exact (HT tr).
Qed.
Theorem agree_frame : forall img_p lim_p en_p img_s lim_s en_s inp (T_p T_s : TSet),
  rz_run img_p lim_p en_p inp T_p -> rz_run img_s lim_s en_s inp T_s -> t_eq T_p T_s ->
  cf_run img_p lim_p en_p inp -> cf_run img_s lim_s en_s inp ->
  error_free (run_scfg ACFG img_p lim_p en_p inp) /\ error_free (run_scfg ACFG img_s lim_s en_s inp) /\
  trace_equiv (bh_traces (run_scfg ACFG img_p lim_p en_p inp)) (bh_traces (run_scfg ACFG img_s lim_s en_s inp)).
Proof.
  intros img_p lim_p en_p img_s lim_s en_s inp T_p T_s Hp Hs HT Cp Cs.
  exact (agree_of_exact img_p lim_p en_p img_s lim_s en_s inp T_p T_s
    (run_exact_of_rz img_p lim_p en_p inp T_p Hp Cp) (run_exact_of_rz img_s lim_s en_s inp T_s Hs Cs) HT).
Qed.
