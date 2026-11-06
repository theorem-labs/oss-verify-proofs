(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AxSymExec3K AsanPlanCoreK AsanPlanK Eb0HSK_0 Eb0HSK_1.
Import APK.
Definition HS_as0 (h : nat) : option acs := match h with 0%nat => Some HS_0 | 1%nat => Some HS_1 | _ => None end.
