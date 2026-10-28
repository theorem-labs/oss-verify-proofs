(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Pj_num_defs Pj_tochars_defs Pj_tochars Pj_dbox Pj_fmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem tochars_proof : tochars_stmt.
Proof. exact (tochars_top dbox_proof fmt_proof). Qed.
