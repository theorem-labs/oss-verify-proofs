(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ubsan_equiv, which Trevor Hansen made from cgif_rgb_fuzzer_ubsan_equiv_shipped and SRC_LIM_MIN_le_shipped_source/target of projects/cgif/cgif_rgb_fuzzer/proofs/lib/UZZ0.v at commit 59c0f6933a6b, at source_alloc_limit and target_alloc_limit, moved here from lib/ConstAccept.v. *)
From Stdlib Require Import ZArith NArith List QArith String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples Omni SpuriousCfg.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier Measure.
From OSSVerify.Core Require Import Images Shapes.
Require OSSVerify.cgif.cgif_rgb_fuzzer.Images.
Require OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.UZZ0.

Lemma ubsan_equiv : strong_universal_error_free_T OSSVerify.cgif.cgif_rgb_fuzzer.Images.plain OSSVerify.cgif.cgif_rgb_fuzzer.Images.ubsan.
Proof.
  intros en_s en_t inp Hs Ht Hv.
  exact (OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.UZZ0.cgif_rgb_fuzzer_ubsan_equiv_lim source_alloc_limit target_alloc_limit
           ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity)
           en_s en_t inp Hs Ht Hv).
Qed.
