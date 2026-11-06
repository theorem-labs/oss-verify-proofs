(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs HeapIface PmLibDefs PmFloatCSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FloatC Require Import SnprintfCps NumFinalC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem snprintf_g_closed : forall {SCFG_P : ScfgP} (L : heap_layout), PMFC.snprintf_g_spec L.
Proof. intros SCFG_P L. exact (snprintf_g_proof L numf_proof). Qed.
