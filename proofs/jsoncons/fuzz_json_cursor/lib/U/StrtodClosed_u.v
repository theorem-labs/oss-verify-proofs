(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs HeapIface CutVF DecIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import DecfloatPre_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import StrtodIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import FloatscanOk_u StrtodOk_u StrtodFinal_u ScanexpOk_u Pm10Leaf_fmodl_u PmLibDefs_u PmLibSpecs_u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module STC.
Section Closed.
Context {SCFG_P : ScfgP}.
Lemma fmodl_ok : CVF.vf_contract PML.RSEGS 0xb4980 192 DFO.IMGc.
Proof. exact (CVF.vf_contract_weaken PML.RSEGS 0xb4980 192 192 None DFO.IMGc ltac:(lia) ltac:(left; reflexivity) Leaf_fmodl_csrc.ok). Qed.
Theorem strtod_closed : forall L : heap_layout, PMS.strtod_spec L PML.STRTOD_SCR_V.
Proof. intros L. exact (STF.strtod_ok fmodl_ok SXO.scanexp_ok L). Qed.
End Closed.
End STC.

