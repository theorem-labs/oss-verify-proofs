(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YM08.v, with its module paths changed; each realizes premise takes a cut_free premise beside it, because fuzz_ctrl's realizes (YK15.v) has a cut at a budget refusal. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed shape_strong_equiv_ef_budgets, shape_strong_equiv_efs_budgets). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK0n YK0i YK15 YK18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import RomStableK RomStableS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Section a. Context {fx : YK11.FPState}.
(* LPS 08b1429: both runs read [run_segments ..] from [init_config (run_segments ..) ..].  Each walk
   is over its binary's own segments and is lifted by [RomStableK.run_init] ([RomStableS.srun_init])
   for an image with no vDSO text ([NoVdso], by computation on a concrete image).  The source run's
   cut-freedom is the run's own (from the statement's budget premise, A/RelimCut.v); the target's
   is its walk's, lifted by [RomStableK.cut_free_run_init]. *)
Theorem shape_strong_equiv_ef_budgets :
forall (ls lt : Z) source_segs rpc rph rsp rbrk rmb rrnd
target_segs apc aph asp abrk amb arnd
(T T' : TSet) (inp : ProcInput)
`{Hvs : NoVdso (mkImage source_segs rpc rph)} `{Hvt : NoVdso (mkImage target_segs apc aph)},
realizes source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd ls inp) T ->
realizes target_segs (init_config target_segs apc aph asp abrk amb arnd lt inp) T' ->
cut_free (run_segments source_segs inp rsp rmb)
  (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd ls inp) ->
cut_free target_segs (init_config target_segs apc aph asp abrk amb arnd lt inp) ->
t_eq T T' ->
strong_equiv_error_free_budgets_scfg ACFG ls lt (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros ls lt source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T T' inp Hvs Hvt
  Hs Ht Cs Ct Heq.
pose proof (run_init source_segs inp rsp rmb rpc rph rbrk rrnd ls T Hvs Hs) as Hs'.
pose proof (run_init target_segs inp asp amb apc aph abrk arnd lt T' Hvt Ht) as Ht'.
pose proof (cut_free_run_init target_segs inp asp amb apc aph abrk arnd lt T' Hvt Ht Ct) as Ct'.
unfold strong_equiv_error_free_budgets_scfg, error_free. cbn.
split; [| split].
- eapply realizes_no_error; [exact Hs' | exact Cs].
- eapply realizes_no_error; [exact Ht' | exact Ct'].
- intro tr.
rewrite (realizes_obs_iff _ _ T Hs' Cs tr).
rewrite (realizes_obs_iff _ _ T' Ht' Ct' tr).
apply Heq.
Qed.
Theorem shape_strong_equiv_efs_budgets :
forall (ls lt : Z) source_segs rpc rph rsp rbrk rmb rrnd
target_segs apc aph asp abrk amb arnd
(T T' : TSet) (inp : ProcInput)
`{Hvs : NoVdso (mkImage source_segs rpc rph)} `{Hvt : NoVdso (mkImage target_segs apc aph)},
realizes source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd ls inp) T ->
srealizes target_segs (init_config target_segs apc aph asp abrk amb arnd lt inp) T' ->
cut_free (run_segments source_segs inp rsp rmb)
  (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd ls inp) ->
t_eq T T' ->
strong_equiv_error_free_budgets_scfg ACFG ls lt (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros ls lt source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T T' inp Hvs Hvt
  Hs Ht Cs Heq.
pose proof (run_init source_segs inp rsp rmb rpc rph rbrk rrnd ls T Hvs Hs) as Hs'.
pose proof (srun_init target_segs inp asp amb apc aph abrk arnd lt T' Hvt Ht) as Ht'.
unfold strong_equiv_error_free_budgets_scfg, error_free. cbn.
split; [| split].
- eapply realizes_no_error; [exact Hs' | exact Cs].
- eapply srealizes_no_error; exact Ht'.
- intro tr.
rewrite (realizes_obs_iff _ _ T Hs' Cs tr).
rewrite (srealizes_obs_iff _ _ T' Ht' tr).
apply Heq.
Qed.
End a.
