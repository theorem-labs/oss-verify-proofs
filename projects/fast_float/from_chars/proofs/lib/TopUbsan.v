(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg RealizesAbort ClfRowsGen.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PTop PAssemble UAssemble ClfTotal.
Require OSSVerify.fast_float.from_chars.images.Plain.
Require OSSVerify.fast_float.from_chars.images.Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem base_ubsan :
  strong_universal_error_free_T_scfg_budgets_abort
    (Run.mkSpuriousCfg false true true true true true)
    ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage OSSVerify.fast_float.from_chars.images.Plain.M.loaded_segments
             OSSVerify.fast_float.from_chars.images.Plain.M.init_pc
             OSSVerify.fast_float.from_chars.images.Plain.M.phdrs)
    (mkImage OSSVerify.fast_float.from_chars.images.Ubsan.M.loaded_segments
             OSSVerify.fast_float.from_chars.images.Ubsan.M.init_pc
             OSSVerify.fast_float.from_chars.images.Ubsan.M.phdrs).
Proof.
  exact (strong_universal_error_free_T_scfg_budgets_abort_shipped _ _ _ _ _ _ _ PTop.SPEC
           PAssemble.plain_realizes_A UAssemble.ubsan_realizes_A PTop.no_kill_SPEC).
Qed.
