(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0n YK0i YK15 YK18 YM08.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YQ02.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Theorem sefb_relim_source : forall (Ls Lbig Lt : Z) (src tgt : Image) (en en' : ExecEntry) (inp : ProcInput),
(Ls <= Lbig)%Z -> ~ run_scfg_budget_refused ACFG src Ls en inp ->
strong_equiv_error_free_budgets_scfg ACFG Lbig Lt src tgt en en' inp ->
strong_equiv_error_free_budgets_scfg ACFG Ls Lt src tgt en en' inp.
Proof.
intros Ls Lbig Lt src tgt en en' inp HLE NB (E1 & E2 & TE). split; [| split].
- exact (run_relim_error_free ACFG src Lbig Ls en inp HLE NB E1).
- exact E2.
- intros tr. rewrite (run_relim_trace_equiv ACFG src Lbig Ls en inp HLE NB tr). exact (TE tr).
Qed.
Section a. Context {fx : YK11.FPState}.
Theorem shape_strong_equiv_ef_relim :
forall (Ls Lbig Lt : Z) source_segs rpc rph rsp rbrk rmb rrnd
target_segs apc aph asp abrk amb arnd
(T T' : TSet) (inp : ProcInput),
(Ls <= Lbig)%Z ->
~ run_scfg_budget_refused ACFG (mkImage source_segs rpc rph) Ls (mkEntry rsp rbrk rmb rrnd) inp ->
realizes source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd Lbig inp) T ->
realizes target_segs (init_config target_segs apc aph asp abrk amb arnd Lt inp) T' ->
t_eq T T' ->
strong_equiv_error_free_budgets_scfg ACFG Ls Lt (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros * HLE NB Hs Ht Heq. apply (sefb_relim_source Ls Lbig Lt _ _ _ _ inp HLE NB).
exact (shape_strong_equiv_ef_budgets Lbig Lt source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T T' inp Hs Ht Heq).
Qed.
Theorem shape_strong_equiv_efs_relim :
forall (Ls Lbig Lt : Z) source_segs rpc rph rsp rbrk rmb rrnd
target_segs apc aph asp abrk amb arnd
(T T' : TSet) (inp : ProcInput),
(Ls <= Lbig)%Z ->
~ run_scfg_budget_refused ACFG (mkImage source_segs rpc rph) Ls (mkEntry rsp rbrk rmb rrnd) inp ->
realizes source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd Lbig inp) T ->
srealizes target_segs (init_config target_segs apc aph asp abrk amb arnd Lt inp) T' ->
t_eq T T' ->
strong_equiv_error_free_budgets_scfg ACFG Ls Lt (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros * HLE NB Hs Ht Heq. apply (sefb_relim_source Ls Lbig Lt _ _ _ _ inp HLE NB).
exact (shape_strong_equiv_efs_budgets Lbig Lt source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T T' inp Hs Ht Heq).
Qed.
End a.
