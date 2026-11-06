(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs PmLibDefs DecIface DecJson StrtodIface FloatscanOk ScanexpOk StrtodClosed Pm10FsInfOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module FSGC.
Section G.
Context {SCFG_P : ScfgP}.
Theorem floatscan_g_ok : FSIC.floatscan_cls_contract PML.RSEGS PDC.src11 (fun t => PDJ.num_final t \/ FSIC.infnan t) 0xb0998.
Proof.
  intros fx R M model K sp F s CAN txt Hh Hl Hfp Rsp Hal Hrng Hdef RF R11 R12 R4 Hret Hfile Hfs Hguard Hgap Htext Htap Hc Herrw Himg HK.
  destruct Hc as [Hnf|Hin].
  - exact (FSO.floatscan_ok STC.fmodl_ok SXO.scanexp_ok fx R M model K sp F s CAN txt Hh Hl Hfp Rsp Hal Hrng Hdef RF R11 R12 R4 Hret Hfile Hfs Hguard Hgap Htext Htap Hnf Herrw Himg HK).
  - exact (FSIC.floatscan_nf_ok fx R M model K sp F s CAN txt Hh Hl Hfp Rsp Hal Hrng Hdef RF R11 R12 R4 Hret Hfile Hfs Hguard Hgap Htext Htap Hin Herrw Himg HK).
Qed.
End G.
End FSGC.

