(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.FinInput.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
Require OSSVerify.yajl_ruby.json_fuzzer.images.Plain.
Require OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import NodesCfg Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import SpecT GlueCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require GlueBudgets.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Clf Require Import ClfTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Lemma acfg_is_cfg : acfg = SpuriousCfgM.cfg.
Proof. reflexivity. Qed.

Section RB.
(* [comment removed for export] *)
Hypothesis RSPEC : realizes_spec_cfg acfg rsegs r_init_pc r_phdrs source_alloc_limit (fun inp => spec (in_argv inp) (in_fs inp)).
Hypothesis BSPEC : realizes_spec_cfg acfg bsegs b_init_pc b_phdrs target_alloc_limit (fun inp => spec (in_argv inp) (in_fs inp)).

Theorem strong_universal_error_free_json_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg
    SpuriousCfgM.cfg
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.phdrs).
Proof. exact (strong_universal_error_free_of_realizes_cfg acfg _ _ _ _ _ _ _ RSPEC BSPEC). Qed.

Let BASE := strong_universal_error_free_json_fuzzer_both.

Lemma src_sat : sat (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.phdrs).
Proof. vm_compute. reflexivity. Qed.
Lemma tgt_sat : sat (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.phdrs).
Proof. vm_compute. reflexivity. Qed.
End RB.

(* [comment removed for export] *)
Section RB_budgets.
Hypothesis RSPEC2 : realizes_spec_cfg acfg rsegs r_init_pc r_phdrs LinuxProcessSemantics.EquivalenceDefinition.Equivalence.sanitizer_source_limit
                                      (fun inp => spec (in_argv inp) (in_fs inp)).
Hypothesis BSPEC : realizes_spec_cfg acfg bsegs b_init_pc b_phdrs target_alloc_limit (fun inp => spec (in_argv inp) (in_fs inp)).

Theorem strong_universal_error_free_json_fuzzer_both_budgets :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.phdrs).
Proof. exact (GlueBudgets.strong_universal_error_free_budgets_of_realizes_cfg_sanitizer acfg _ _ _ _ _ _ _ RSPEC2 BSPEC). Qed.
End RB_budgets.
