(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs HeapIface. From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmFloatCSpecs_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.FloatC Require Import SnprintfCps_u NumFinalC_u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem snprintf_g_closed : forall {SCFG_P : ScfgP} (L : heap_layout), PMFC.snprintf_g_spec L.
Proof. intros SCFG_P L. exact (snprintf_g_proof L numf_proof). Qed.
