(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeEF ShapeSpec TopUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Glue Require Import Top04.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg AMainEntry ABoot.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require ShapeAlg SpinAlg AsanPlanImages AsanInit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation psegs := OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.loaded_segments (only parsing).
Local Notation ppc := OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.init_pc (only parsing).
Local Notation pph := OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.phdrs (only parsing).

Definition ASAN : Image :=
  mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.

(* [comment removed for export] *)
Theorem shape_strong_equiv_sef_AS :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  AS.SpinAlg.srealizes target_segs (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim T inp Hsource Htarget.
  split; [| split].
  - cbn. eapply realizes_no_error; exact Hsource.
  - cbn. eapply AS.SpinAlg.srealizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff source_segs _ T Hsource tr).
    rewrite (AS.SpinAlg.srealizes_obs_iff target_segs _ T Htarget tr).
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma asan_triple_lim : a_main_stmt -> forall (lim : Z), (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.drv_limit <= lim)%Z ->
  forall en_source en_target inp,
    valid_entry SRC0 en_source inp -> valid_entry ASAN en_target inp -> valid_input inp ->
    error_free (run_scfg ACFG SRC0 lim en_source inp)
    /\ error_free (run_scfg ACFG ASAN target_alloc_limit en_target inp)
    /\ trace_equiv (bh_traces (run_scfg ACFG SRC0 lim en_source inp)) (bh_traces (run_scfg ACFG ASAN target_alloc_limit en_target inp)).
Proof.
  intros HA lim Hlim [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hinp.
  apply (shape_strong_equiv_sef_AS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec04 (in_argv inp) (in_fs inp))).
  - exact (plain_realizes04_lim lim Hlim rsp rbrk rmb rrnd inp Hens Hinp).
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hent as [Hsp [Hbrk [Hmb Hfit]]].
    (* [comment removed for export] *)
    destruct Hinp as (Hargv & Henvp & Hfs & _ & (Huid & _) & _ & _ & Hhw & _ & Hvs & _).
    destruct inp as [argv envp ifs stdin uid gid groups net nof sigm hw abt vs urnd tmp].
    cbn [in_argv in_envp in_fs in_image_fs in_tmp in_uid in_hwcap in_va_size] in *. subst vs.
    exact (a_boot HA asp abrk amb arnd argv envp ifs stdin uid gid hw groups net nof sigm abt urnd tmp Hsp Hbrk Hmb Hargv Henvp Hfs Hfit Huid Hhw).
Qed.

(* [comment removed for export] *)
Theorem asan_base_of : a_main_stmt -> strong_universal_error_free_T_scfg ACFG SRC0 ASAN.
Proof.
  intros HA en_source en_target inp Hens Hent Hinp.
  refine (asan_triple_lim HA source_alloc_limit _ en_source en_target inp Hens Hent Hinp).
  unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.drv_limit, source_alloc_limit. lia.
Qed.

(* [comment removed for export] *)
Theorem asan_base_of_budgets : a_main_stmt ->
  strong_universal_error_free_T_scfg_budgets ACFG source_alloc_limit target_alloc_limit SRC0 ASAN.
Proof. intros HA. apply strong_universal_error_free_T_scfg_budgets_of_scfg. exact (asan_base_of HA). Qed.

(* [comment removed for export] *)
Theorem asan_base_of_san : a_main_stmt ->
  strong_universal_error_free_T_scfg_budgets ACFG sanitizer_source_limit target_alloc_limit SRC0 ASAN.
Proof.
  intros HA en_source en_target inp Hens Hent Hinp _.
  exact (asan_triple_lim HA sanitizer_source_limit sanitizer_limit_ok en_source en_target inp Hens Hent Hinp).
Qed.
