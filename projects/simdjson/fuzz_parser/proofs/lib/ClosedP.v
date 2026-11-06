(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import TopLevel PlainTopU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import TopLevelGen.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require AsanMainU BothMainU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg PlainClosed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg UbsanClosed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require AImg ADriver_iface AMain_final.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require BImg ADriver_iface AMain_final.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module AF := OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW.AMain_final.
Module BF := OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW.AMain_final.
Module AI := OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW.AImg.
Module BI := OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW.BImg.
Module AD := OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW.ADriver_iface.
Module BD := OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW.ADriver_iface.

(* [comment removed for export] *)
Lemma plain_side : plain_client_stmt -> side_ok psegs p_init_pc p_phdrs source_alloc_limit TSU.
Proof. intros PC. exact (plain_side_ok (plain_impl_closed_modulo_client PC)). Qed.

(* [comment removed for export] *)
Lemma plain_side_san : plain_client_stmt -> side_ok psegs p_init_pc p_phdrs SanitizerBudgets.lim_source TSU.
Proof. intros PC. exact (plain_side_ok_san (plain_impl_closed_modulo_client PC)). Qed.

(* [comment removed for export] *)
Theorem base_ubsan_mc : plain_client_stmt -> ubsan_client_stmt ->
  strong_universal_error_free_T_scfg_budgets_abort ACFG ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs) (mkImage usegs u_init_pc u_phdrs).
Proof. intros PC UC. exact (base_ubsan (plain_impl_closed_modulo_client PC) (ubsan_impl_closed_modulo_client UC)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem base_asan_mc : plain_client_stmt -> AF.asan_client_stmt ->
  strong_universal_error_free_T_scfg_budgets_abort ACFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs) (mkImage AI.asegs AI.a_init_pc AI.a_phdrs).
Proof.
  intros PC AC. eapply (side_ok_equiv_budgets_abort_lim _ _ _ _ _ _ _ _ TSU TSU);
    [exact (plain_side_san PC) | exact (AsanMainU.target_side SPEC_nil AD.ASTAGE (AF.asan_impl_final AC)) | exact NOKILL |].
  intros enS enT inp HvS HvT Hi tr. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem base_both_mc : plain_client_stmt -> BF.asan_client_stmt ->
  strong_universal_error_free_T_scfg_budgets_abort ACFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs) (mkImage BI.bsegs BI.b_init_pc BI.b_phdrs).
Proof.
  intros PC BC. eapply (side_ok_equiv_budgets_abort_lim _ _ _ _ _ _ _ _ TSU TSU);
    [exact (plain_side_san PC) | exact (BothMainU.target_side SPEC_nil BD.ASTAGE (BF.both_impl_final BC)) | exact NOKILL |].
  intros enS enT inp HvS HvT Hi tr. reflexivity.
Qed.
