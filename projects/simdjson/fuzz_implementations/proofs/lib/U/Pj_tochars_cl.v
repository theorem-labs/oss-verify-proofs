(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Pj_num_defs Pj_tochars_defs Pj_tochars Pj_dbox Pj_fmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem tochars_proof : tochars_stmt.
Proof. exact (tochars_top dbox_proof fmt_proof). Qed.
