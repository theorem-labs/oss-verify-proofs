(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the certificates are stated once per CONFIG_RSEQ layout, one forest per layout checked at that layout's table, and the start-up's holes and blob-freedom lemmas moved to StartupCertBoth. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require BoLibFuzz.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO BothAsanPlanImages AsanInit AsanMainLib AsanMainHooksBoth AsanMainDefsBoth AsanMainTreeBoth
  AsanMainCertLibBoth AsanMainItabBoth StartHooksBoth StartupPlanBoth StartupHSBoth StartupCertBoth.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import InfoBothTop.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import APC. Import AP.

Section Final.
  (* [comment removed for export] *)
  (* LPS 727298f3: one forest per CONFIG_RSEQ layout [rsb], each checked at that layout's table;
     the start-up's certificate, shape, holes and blob-freedom are [StartupCertBoth]'s, per layout. *)
  Variable TREE : bool -> nat -> nat -> mtree.
  Hypothesis TREES : forall rsb h ch i, HS_both rsb h = Some ch -> (i < 6)%nat ->
    mtree_ok (rseq_z rsb) KCm BFUELm FUELm ITmD 0 0 (HSA (HS_both rsb) h) (root_class i) (TREE rsb h i) = true.

  Definition info_both_certs : both_certs :=
    BOTH_CERTS IT0 IT0_ok HS_both startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_all_holes HSA_noblob
               KCm BFUELm FUELm ITmD ITmD_ok TREE TREES.

  (* [comment removed for export] *)
  Theorem info_both_final :
    strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
      SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc
               Plain.M.phdrs)
      (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc
               AsanUbsan.M.phdrs).
  Proof. exact (info_both_top_closed info_both_certs). Qed.

  (* [comment removed for export] *)
  Definition info_both_final_ca_iff := info_both_ca_iff_closed info_both_certs.
  Definition info_both_final_cb_iff := info_both_cb_iff_closed info_both_certs.
End Final.
