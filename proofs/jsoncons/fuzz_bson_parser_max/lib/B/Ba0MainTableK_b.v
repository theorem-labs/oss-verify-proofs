(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0HSK_0_b Ba0HSK_1_b.
Import APK.
Definition HS_as0 (h : nat) : option acs := match h with 0%nat => Some HS_0 | 1%nat => Some HS_1 | _ => None end.
