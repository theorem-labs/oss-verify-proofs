(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec DvB_ExitPreT.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Lemma pre_T2_ok : pre_flush_chk 2 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ax_flush_2 `{fx : DFP} := @ax_flush fx 2 ltac:(lia) pre_T2_ok.
