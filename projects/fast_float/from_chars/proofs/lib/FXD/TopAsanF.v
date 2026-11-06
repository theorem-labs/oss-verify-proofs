(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg RealizesAbort ClfRowsGen.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PTop PAssemble ClfTotal.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTop AsanTopF.
Require OSSVerify.fast_float.from_chars.images.Plain.
Require OSSVerify.fast_float.from_chars.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation DCFG := (Run.mkSpuriousCfg false true true true true true).

Section File.
Hypothesis Hleaves : ltac:(let t := type of (AsanTopF.h_file DCFG eq_refl eq_refl) in
                             lazymatch t with ?A -> _ => exact A end).
Definition H_file := AsanTopF.h_file DCFG eq_refl eq_refl Hleaves.

#[using="Hleaves"] Theorem asan_realizes_D :
  image_realizes_cfg_e DCFG OSSVerify.fast_float.from_chars.images.Asan.M.loaded_segments
    OSSVerify.fast_float.from_chars.images.Asan.M.init_pc
    OSSVerify.fast_float.from_chars.images.Asan.M.phdrs target_alloc_limit PTop.SPEC.
Proof. LiaFast.lf_pins (fun (Hleaves : LiaFast.U) => LiaFast.u0). exact (AsanTop.asan_realizes DCFG eq_refl eq_refl H_file). Qed.

#[using="Hleaves"] Theorem base_asan_from :
  strong_universal_error_free_T_scfg_budgets_abort DCFG
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OSSVerify.fast_float.from_chars.images.Plain.M.loaded_segments
             OSSVerify.fast_float.from_chars.images.Plain.M.init_pc
             OSSVerify.fast_float.from_chars.images.Plain.M.phdrs)
    (mkImage OSSVerify.fast_float.from_chars.images.Asan.M.loaded_segments
             OSSVerify.fast_float.from_chars.images.Asan.M.init_pc
             OSSVerify.fast_float.from_chars.images.Asan.M.phdrs).
Proof. LiaFast.lf_pins (fun (Hleaves : LiaFast.U) => LiaFast.u0).
  exact (strong_universal_error_free_T_scfg_budgets_abort_sanitizer _ _ _ _ _ _ _ PTop.SPEC
           PAssemble.plain_realizes_A_san asan_realizes_D PTop.no_kill_SPEC).
Qed.
End File.
