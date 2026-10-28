(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import L5Defs HeapIface CutVF. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecIface_u5 DecfloatPre_u5 StrtodIface_u5 FloatscanOk_u5 StrtodOk_u5 PmLibDefs_u5 PmLibSpecs_u5.
Open Scope Z_scope.
Module STF.
Section Final.
Context {SCFG_P : ScfgP}.
Hypothesis FMODL : CVF.vf_contract PML.RSEGS 0xbb134 192 DFO.IMGc.
Hypothesis SCX : PDC.scanexp_contract PML.RSEGS PDC.src11.
Theorem strtod_ok : forall L : heap_layout, PMS.strtod_spec L PML.STRTOD_SCR_V.
Proof. intros L. exact (STO.strtod_ok (FSO.floatscan_ok FMODL SCX) L). Qed.
End Final.
End STF.
Print Assumptions STF.strtod_ok.
