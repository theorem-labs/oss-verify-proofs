(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs HeapIface CutVF DecIface DecfloatPre StrtodIface FloatscanOk StrtodOk PmLibDefs PmLibSpecs.
Open Scope Z_scope.
Module STF.
Section Final.
Context {SCFG_P : ScfgP}.
Hypothesis FMODL : CVF.vf_contract PML.RSEGS 0xb2b2c 192 DFO.IMGc.
Hypothesis SCX : PDC.scanexp_contract PML.RSEGS PDC.src11.
Theorem strtod_ok : forall L : heap_layout, PMS.strtod_spec L PML.STRTOD_SCR_V.
Proof. intros L. exact (STO.strtod_ok (FSO.floatscan_ok FMODL SCX) L). Qed.
End Final.
End STF.

