(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
Require OSSVerify.yajl_ruby.json_fuzzer.images.Asan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling Nodes NodesCfg Images RunInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import SpecT GlueCfg R_TopCfg HaltsGen HaltsSpec HaltsGlue HaltsGlueLim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.TopA Require Import A_TopCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Lemma A_realizes_init : forall en inp,
  valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input inp ->
  realizes_cfg acfg asegs
    (init_config asegs a_init_pc a_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
       target_alloc_limit inp)
    (spec (in_argv inp) (in_fs inp)).
Proof.
  intros en inp VE VI.
  apply (A_MAIN_REACH en inp (spec (in_argv inp) (in_fs inp)) VE VI (spec_nil _ _)).
  intros E0 FSB0 PL0 HR0 L0 RES0 EB0 FULL model ms ENV0 PL0OK MF MOFS MOFD MM.
  exact (a_main_rz en inp VE VI E0 FSB0 PL0 HR0 L0 RES0 EB0 FULL model ms ENV0 PL0OK MF MOFS MOFD MM).
Qed.

Theorem halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    [Z_to_bv 64 0; Z_to_bv 64 2]
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Asan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Asan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Asan.M.phdrs).
Proof.
  apply (halts_allowed_of_realizes_init_big acfg asegs a_init_pc a_phdrs target_alloc_limit source_alloc_limit
           halts_codes (fun inp => spec (in_argv inp) (in_fs inp))).
  - unfold source_alloc_limit, target_alloc_limit. lia.
  - exact A_realizes_init.
  - intros inp _. apply spec_exits_in.
Qed.
