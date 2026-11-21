(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed shape_strong_equiv_ef, shape_strong_equiv_ef_eq. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0n YK0i YK15.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.R Require Import Cfg.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.Cfg Require Import RomStable.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Section a. Context {fx : YK11.FPState}.
Theorem shape_strong_equiv_ef :
forall source_segs rpc rph rsp rbrk rmb rrnd
target_segs apc aph asp abrk amb arnd
(T : TSet) (inp : ProcInput),
realizes source_segs
(init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp) T ->
realizes target_segs
(init_config target_segs apc aph asp abrk amb arnd target_alloc_limit inp) T ->
vdso_image source_segs = None -> vdso_image target_segs = None ->
strong_equiv_error_free_scfg ACFG (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T inp Hs Ht Hvs Hvt.
(* LPS 08b1429: both runs start from [init_config (run_segments ..) ..] ([Cfg.RomStable.run_init]) *)
pose proof (run_init source_segs inp rsp rmb rpc rph rbrk rrnd source_alloc_limit T Hvs Hs) as Hs'.
pose proof (run_init target_segs inp asp amb apc aph abrk arnd target_alloc_limit T Hvt Ht) as Ht'.
unfold strong_equiv_error_free_scfg, error_free. cbn.
split; [| split].
- eapply realizes_no_error; exact Hs'.
- eapply realizes_no_error; exact Ht'.
- intro tr.
rewrite (realizes_obs_iff _ _ T Hs' tr).
rewrite (realizes_obs_iff _ _ T Ht' tr).
reflexivity.
Qed.
Corollary shape_strong_equiv_ef_eq :
forall source_segs rpc rph rsp rbrk rmb rrnd
target_segs apc aph asp abrk amb arnd
(T T' : TSet) (inp : ProcInput),
realizes source_segs
(init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp) T ->
realizes target_segs
(init_config target_segs apc aph asp abrk amb arnd target_alloc_limit inp) T' ->
t_eq T T' ->
vdso_image source_segs = None -> vdso_image target_segs = None ->
strong_equiv_error_free_scfg ACFG (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros * Hs Ht Heq Hvs Hvt.
eapply shape_strong_equiv_ef; [| exact Ht | exact Hvs | exact Hvt].
eapply rz_conseq; [exact Hs | exact Heq].
Qed.
End a.
