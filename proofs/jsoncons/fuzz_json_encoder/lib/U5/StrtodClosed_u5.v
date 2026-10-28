(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import L5Defs HeapIface CutVF. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecIface_u5 DecfloatPre_u5 StrtodIface_u5 FloatscanOk_u5 StrtodOk_u5 StrtodFinal_u5 ScanexpOk_u5 Pm6Leaf_fmodl_u5 PmLibDefs_u5 PmLibSpecs_u5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module STC.
Section Closed.
Context {SCFG_P : ScfgP}.
Lemma fmodl_ok : CVF.vf_contract PML.RSEGS 0xbb134 192 DFO.IMGc.
Proof. exact (CVF.vf_contract_weaken PML.RSEGS 0xbb134 192 192 None DFO.IMGc ltac:(lia) ltac:(left; reflexivity) Leaf_fmodl_xsrc.ok). Qed.
Theorem strtod_closed : forall L : heap_layout, PMS.strtod_spec L PML.STRTOD_SCR_V.
Proof. intros L. exact (STF.strtod_ok fmodl_ok SXO.scanexp_ok L). Qed.
End Closed.
End STC.
Print Assumptions STC.strtod_closed.
