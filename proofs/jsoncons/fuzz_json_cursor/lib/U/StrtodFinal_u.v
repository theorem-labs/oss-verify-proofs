(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs HeapIface CutVF DecIface DecIfaceU. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import DecfloatPre_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import StrtodIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import FloatscanOk_u StrtodOk_u PmLibDefs_u PmLibSpecs_u.
Open Scope Z_scope.
Module STF.
Section Final.
Context {SCFG_P : ScfgP}.
Hypothesis FMODL : CVF.vf_contract PML.RSEGS 0xb4980 192 DFO.IMGc.
Hypothesis SCX : PDC.scanexp_contract PML.RSEGS PDCU.ubsan11.
Theorem strtod_ok : forall L : heap_layout, PMS.strtod_spec L PML.STRTOD_SCR_V.
Proof. intros L. exact (STO.strtod_ok (FSO.floatscan_ok FMODL SCX) L). Qed.
End Final.
End STF.

