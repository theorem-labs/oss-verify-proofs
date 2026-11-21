From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import RomStableK.
Import ListNotations.
Definition run_exact (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) (T : list event -> Prop) : Prop :=
  error_free (run_scfg ACFG img lim en inp) /\ forall tr, bh_traces (run_scfg ACFG img lim en inp) tr <-> T tr.
(* [rz_run] and [cf_run] are a walk over the binary's own segments, from the binary's start.  At
   LPS 08b1429 the run reads [run_segments segs ..] from [init_config (run_segments ..) ..]; the
   theorems below lift both through [RomStableK] ([run_init], [cut_free_run_init]), for an image
   with no vDSO text of its own ([NoVdso], by computation on a concrete image). *)
Definition rz_run (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) (T : TSet) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd => realizes segs (init_config segs pc ph sp brk0 mbase rnd lim inp) T
  end.
Definition cf_run (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd => cut_free segs (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.
Theorem run_exact_of_rz (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) (T : TSet)
  {Hv : NoVdso img} :
  rz_run img lim en inp T -> cf_run img lim en inp -> run_exact img lim en inp T.
Proof.
  destruct img as [segs pc ph], en as [sp brk0 mbase rnd]. intros HR HC.
  pose proof (run_init segs inp sp mbase pc ph brk0 rnd lim T Hv HR) as HR'.
  pose proof (cut_free_run_init segs inp sp mbase pc ph brk0 rnd lim T Hv HR HC) as HC'.
  split.
  - exact (realizes_no_error _ _ T HR' HC').
  - exact (realizes_obs_iff _ _ T HR' HC').
Qed.
Theorem run_exact_of_rz_budget (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) (T : TSet)
  {Hv : NoVdso img} :
  rz_run img lim en inp T -> ~ run_scfg_budget_refused ACFG img lim en inp -> run_exact img lim en inp T.
Proof.
  destruct img as [segs pc ph], en as [sp brk0 mbase rnd]. intros HR HB.
  pose proof (run_init segs inp sp mbase pc ph brk0 rnd lim T Hv HR) as HR'.
  pose proof (cut_free_intro (run_segments segs inp sp mbase)
    (init_config (run_segments segs inp sp mbase) pc ph sp brk0 mbase rnd lim inp) HB) as HC'.
  split.
  - exact (realizes_no_error _ _ T HR' HC').
  - exact (realizes_obs_iff _ _ T HR' HC').
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
(* The source side is cut-free by the statement's budget premise over the run; the target side by
   its walk ([cf_run]). *)
Theorem agree_frame (img_p : Image) (lim_p : Z) (en_p : ExecEntry) (img_s : Image) (lim_s : Z)
  (en_s : ExecEntry) (inp : ProcInput) (T_p T_s : TSet) {Hvp : NoVdso img_p} {Hvs : NoVdso img_s} :
  rz_run img_p lim_p en_p inp T_p -> rz_run img_s lim_s en_s inp T_s -> t_eq T_p T_s ->
  ~ run_scfg_budget_refused ACFG img_p lim_p en_p inp -> cf_run img_s lim_s en_s inp ->
  error_free (run_scfg ACFG img_p lim_p en_p inp) /\ error_free (run_scfg ACFG img_s lim_s en_s inp) /\
  trace_equiv (bh_traces (run_scfg ACFG img_p lim_p en_p inp)) (bh_traces (run_scfg ACFG img_s lim_s en_s inp)).
Proof.
  intros Hp Hs HT Bp Cs.
  exact (agree_of_exact img_p lim_p en_p img_s lim_s en_s inp T_p T_s
    (run_exact_of_rz_budget img_p lim_p en_p inp T_p Hp Bp) (run_exact_of_rz img_s lim_s en_s inp T_s Hs Cs) HT).
Qed.
