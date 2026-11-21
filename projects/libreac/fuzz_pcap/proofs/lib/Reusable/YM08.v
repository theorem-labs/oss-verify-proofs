(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YM08.v, with its module paths changed; each realizes premise takes a cut_free premise beside it, because fuzz_pcap's realizes (YK15.v) has a cut at a budget refusal. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3, with libreac/fuzz_boxreg's port of its copy of this file (changed shape_strong_equiv_ef_budgets, shape_strong_equiv_efs_budgets). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK0n YK0i YK15 YK18.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import RomStableK RomStableS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Section a. Context {fx : YK11.FPState}.
Theorem shape_strong_equiv_ef_budgets :
forall (ls lt : Z) source_segs rpc rph rsp rbrk rmb rrnd
target_segs apc aph asp abrk amb arnd
(T T' : TSet) (inp : ProcInput)
(* LPS 08b1429: both runs start from [init_config (run_segments ..) ..]; each walk and its
   cut-freeness are lifted by [RomStableK] ([run_init], [cut_free_run_init]), which asks that the
   binary carries no vDSO text of its own.  As instance arguments, so that a caller on a concrete
   image needs no new argument ([NoVdso]'s hint closes them by computation). *)
`{NoVdso (mkImage source_segs rpc rph)} `{NoVdso (mkImage target_segs apc aph)},
realizes source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd ls inp) T ->
realizes target_segs (init_config target_segs apc aph asp abrk amb arnd lt inp) T' ->
(* the source side comes from [RelimCut.cut_free_of_relim], which is run-level already *)
cut_free (run_segments source_segs inp rsp rmb)
  (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd ls inp) ->
cut_free target_segs (init_config target_segs apc aph asp abrk amb arnd lt inp) ->
t_eq T T' ->
strong_equiv_error_free_budgets_scfg ACFG ls lt (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
(* 08b1429: the two `{NoVdso ...} instance binders above are introduced POSITIONALLY by intros,
   so they need two names of their own; without them Hs/Ht captured the instances and every
   later name shifted by two. *)
intros ls lt source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T T' inp NVs NVt Hs Ht Cs Ct Heq.
pose proof (run_init source_segs inp rsp rmb rpc rph rbrk rrnd ls T (no_vdso (img:=mkImage source_segs rpc rph)) Hs) as Hs'.
pose proof (run_init target_segs inp asp amb apc aph abrk arnd lt T' (no_vdso (img:=mkImage target_segs apc aph)) Ht) as Ht'.
pose proof Cs as Cs'.
pose proof (cut_free_run_init target_segs inp asp amb apc aph abrk arnd lt T' (no_vdso (img:=mkImage target_segs apc aph)) Ht Ct) as Ct'.
unfold strong_equiv_error_free_budgets_scfg, error_free. cbn.
split; [| split].
- eapply realizes_no_error; [exact Hs' | exact Cs'].
- eapply realizes_no_error; [exact Ht' | exact Ct'].
- intro tr.
rewrite (realizes_obs_iff _ _ T Hs' Cs' tr).
rewrite (realizes_obs_iff _ _ T' Ht' Ct' tr).
apply Heq.
Qed.
Theorem shape_strong_equiv_efs_budgets :
forall (ls lt : Z) source_segs rpc rph rsp rbrk rmb rrnd
target_segs apc aph asp abrk amb arnd
(T T' : TSet) (inp : ProcInput)
`{NoVdso (mkImage source_segs rpc rph)} `{NoVdso (mkImage target_segs apc aph)},
realizes source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd ls inp) T ->
srealizes target_segs (init_config target_segs apc aph asp abrk amb arnd lt inp) T' ->
cut_free (run_segments source_segs inp rsp rmb)
  (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd ls inp) ->
t_eq T T' ->
strong_equiv_error_free_budgets_scfg ACFG ls lt (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros ls lt source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T T' inp NVs NVt Hs Ht Cs Heq.
pose proof (run_init source_segs inp rsp rmb rpc rph rbrk rrnd ls T (no_vdso (img:=mkImage source_segs rpc rph)) Hs) as Hs'.
pose proof (srun_init target_segs inp asp amb apc aph abrk arnd lt T' (no_vdso (img:=mkImage target_segs apc aph)) Ht) as Ht'.
pose proof Cs as Cs'.
unfold strong_equiv_error_free_budgets_scfg, error_free. cbn.
split; [| split].
- eapply realizes_no_error; [exact Hs' | exact Cs'].
- eapply srealizes_no_error; exact Ht'.
- intro tr.
rewrite (realizes_obs_iff _ _ T Hs' Cs' tr).
rewrite (srealizes_obs_iff _ _ T' Ht' tr).
apply Heq.
Qed.
End a.
