(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import DecIface DecIfaceU DecJson StrtodIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import FloatscanOk_u ScanexpOk_u StrtodClosed_u Pm10FsInfOk_u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module FSGC.
Section G.
Context {SCFG_P : ScfgP}.
Theorem floatscan_g_ok : FSIC.floatscan_cls_contract PML.RSEGS PDCU.ubsan11 (fun t => PDJ.num_final t \/ FSIC.infnan t) 0xb27ec.
Proof.
  intros fx R M model K sp F s CAN txt Hh Hl Hfp Rsp Hal Hrng Hdef RF R11 R12 R4 Hret Hfile Hfs Hguard Hgap Htext Htap Hc Herrw Himg HK.
  destruct Hc as [Hnf|Hin].
  - exact (FSO.floatscan_ok STC.fmodl_ok SXO.scanexp_ok fx R M model K sp F s CAN txt Hh Hl Hfp Rsp Hal Hrng Hdef RF R11 R12 R4 Hret Hfile Hfs Hguard Hgap Htext Htap Hnf Herrw Himg HK).
  - exact (FSIC.floatscan_nf_ok fx R M model K sp F s CAN txt Hh Hl Hfp Rsp Hal Hrng Hdef RF R11 R12 R4 Hret Hfile Hfs Hguard Hgap Htext Htap Hin Herrw Himg HK).
Qed.
End G.
End FSGC.

