(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Asan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Spec SpecExits.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require SpinAlg AsanPlanSound AsanPlanImages AsanCertDefs AsanInit AsanMainEntryFacts AsanBoot.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require AImg A_main_top.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib Require Import TopAsan FinalAsan TopHaltsAsan.

(* [comment removed for export] *)
Lemma HSEGS_ASEGS : HSEGS = AsanCertDefs.ASEGS.
Proof. reflexivity. Qed.
Lemma LIMIT_is_target : AsanInit.LIMIT = target_alloc_limit.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma asan_realizes_spec : asan_realizes_spec_stmt.
Proof.
  intros sp brk0 mbase rdraw inp Vsp Vbrk Va Ve Vfit Vuid Vab Vva Vhw.
  rewrite HSEGS_ASEGS, <- AsanBoot.APH_is_phdrs, <- LIMIT_is_target.
  apply (AsanBoot.asan_boot_entry_inp sp brk0 mbase rdraw inp Vsp Vbrk Va Ve Vfit Vuid Vab Vva
           (fun _ _ => Spec.spec (in_argv inp) (in_fs inp))).
  - intros; reflexivity.
  - intros E fs'. apply SpecExits.spec_has_nil.
  - intros R mem md E _ HME Hfs. rewrite ASEGS_asegs, cfg_of_mkCfg.
    exact (A_main_top.A_main_stmt_of_bridge _ (in_argv inp) (in_fs inp) sp
             (asan_bridge sp brk0 rdraw (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp) Vsp Va Ve Vfit Vuid Vhw)
             R mem md HME Hfs).
Qed.

(* [comment removed for export] *)
Theorem halts_asan_assembled :
  halts_allowed_T_scfg_budgets forced_only_cfg Equivalence.ShippedBudgets.lim_source SpecExits.codes02 TopHaltsAsan.asan_img.
Proof. exact (halts_asan_of_realizes asan_realizes_spec). Qed.

(* [comment removed for export] *)
