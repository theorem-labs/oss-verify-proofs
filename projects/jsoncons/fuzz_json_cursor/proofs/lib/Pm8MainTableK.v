(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed HS_as0. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK Pm8HSK_0 Pm8HSK_1.
Import APK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* STATEMENT CHANGED: indexed by the CONFIG_RSEQ flag (OLD [HS_as0 h]). *)
Definition HS_as0 (b : bool) (h : nat) : option acs := match h with 0%nat => Some (HS_0 b) | 1%nat => Some (HS_1 b) | _ => None end.
