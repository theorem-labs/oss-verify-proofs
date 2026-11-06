(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require MsgpackEncImgFacts MsgpackEncFinalS MsgpackEncAsanTop. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncImgFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncFinalS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncAsanTop. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record open_asan : Prop := OPEN_ASAN { oa_src : open_S; oa_tgt : as0_tgt_stmt cfg0 }.

Section Rows.
Hypothesis OA : open_asan.

(* [comment removed for export] *)
Theorem msgpack_enc_asan_base :
  strong_universal_error_free_T_scfg cfg0
    (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.loaded_segments OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.init_pc OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.phdrs)
    (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.loaded_segments OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.init_pc OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.phdrs).
Proof. exact (msgpack_enc_asan_final_scfg (oa_src OA) (oa_tgt OA)). Qed.

(* [comment removed for export] *)
Theorem msgpack_enc_asan_base_abort :
  strong_universal_error_free_T_scfg_budgets_abort cfg0 SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.loaded_segments OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.init_pc OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.phdrs)
    (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.loaded_segments OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.init_pc OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.phdrs).
Proof. exact (msgpack_enc_asan_final_abort (oa_src OA) (oa_tgt OA)). Qed.

End Rows.

