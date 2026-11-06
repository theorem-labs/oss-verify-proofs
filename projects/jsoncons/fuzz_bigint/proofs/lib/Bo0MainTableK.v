(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK Bo0HSK_0 Bo0HSK_1.
Import APK.
Definition HS_as0 (h : nat) : option acs := match h with 0%nat => Some HS_0 | 1%nat => Some HS_1 | _ => None end.
