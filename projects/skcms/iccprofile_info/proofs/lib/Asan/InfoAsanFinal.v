(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsLibFuzz.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO AsanPlanImages AsanInit AsanInitHW AsanMainLib AsanMainDefs AsanMainTree
  AsanMainCertLib AsanMainItab StartHooks StartupPlanAsan StartupHSAsan StartupCertAsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import InfoAsanTop.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import APC. Import AP.

(* [comment removed for export] *)
Lemma startup_all_holes : all_holes startup_shape = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma HS0_noblob : match HS0 with Some ch => acs_noblob ch | None => true end = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma HSA_noblob : forall h ch, HS_asan h = Some ch -> acs_noblob ch = true.
Proof.
  intros [|h] ch H; [|discriminate H].
  change (HS0 = Some ch) in H. pose proof HS0_noblob as P. rewrite H in P. exact P.
Qed.

Section Final.
  (* [comment removed for export] *)
  Variable TREE : nat -> nat -> mtree.
  Hypothesis TREES : forall h ch i, HS_asan h = Some ch -> (i < 6)%nat ->
    mtree_ok KCm BFUELm FUELm ITmD 0 0 (HSA HS_asan h) (root_class i) (TREE h i) = true.

  Definition info_asan_certs : asan_certs :=
    ASAN_CERTS IT0 IT0_ok HS_asan startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_all_holes HSA_noblob
               KCm BFUELm FUELm ITmD ITmD_ok TREE TREES.

  (* [comment removed for export] *)
  Theorem info_asan_final :
    strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
      SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc
               Plain.M.phdrs)
      (mkImage Asan.M.loaded_segments Asan.M.init_pc
               Asan.M.phdrs).
  Proof. exact (info_asan_top_closed info_asan_certs). Qed.

  (* [comment removed for export] *)
  Definition info_asan_final_ca_iff := info_asan_ca_iff_closed info_asan_certs.
  Definition info_asan_final_cb_iff := info_asan_cb_iff_closed info_asan_certs.
End Final.
