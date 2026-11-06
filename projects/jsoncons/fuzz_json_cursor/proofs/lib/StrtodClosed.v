(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs HeapIface CutVF DecIface DecfloatPre StrtodIface FloatscanOk StrtodOk StrtodFinal ScanexpOk Pm10Leaf_fmodl PmLibDefs PmLibSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module STC.
Section Closed.
Context {SCFG_P : ScfgP}.
Lemma fmodl_ok : CVF.vf_contract PML.RSEGS 0xb2b2c 192 DFO.IMGc.
Proof. exact (CVF.vf_contract_weaken PML.RSEGS 0xb2b2c 192 192 None DFO.IMGc ltac:(lia) ltac:(left; reflexivity) Leaf_fmodl_csrc.ok). Qed.
Theorem strtod_closed : forall L : heap_layout, PMS.strtod_spec L PML.STRTOD_SCR_V.
Proof. intros L. exact (STF.strtod_ok fmodl_ok SXO.scanexp_ok L). Qed.
End Closed.
End STC.

