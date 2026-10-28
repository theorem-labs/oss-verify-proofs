(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import L5Defs HeapIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmFloatXSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FloatX Require Import SnprintfCpsX_u5 NumFinalCX_u5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem snprintf_g_closed : forall {SCFG_P : ScfgP} (L : heap_layout), PMFX.snprintf_g_spec L.
Proof. intros SCFG_P L. exact (snprintf_g_proof L numf_proof). Qed.
