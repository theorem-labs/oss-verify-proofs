(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The ubsan target half for the library layout Lay0U and statics PMX.pm_staticsx: everything but the library's call
   contract (LCU.lib_iface_okU at PHI0U) is discharged. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec SpinAlg HeapIface LibIface.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibSpecsX_u5 PmXubsanStmt PmXubsanTgtW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopGlueU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require Import LibContractU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapInstU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmXubsanTgtLay.
Import PmXubsanStmt.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Section Lay.
  (* The ubsan library's call contract over Lay0U (s-int's PmLibInstU.lib_iface0U). *)
  Hypothesis LIBU : forall sp, valid_sp sp ->
    LCU.lib_iface_okU (TopGlueU.Lay0U (bv_unsigned sp)) cfgU (HIU (bv_unsigned sp)) PMX.pm_staticsx PHI0U.

  Theorem pm_xubsan_tgt0 : pm_xubsan_tgt_stmt cfgU PHI0U.
  Proof.
    apply (PmXubsanTgtW.pm_xubsan_tgt (fun sp => TopGlueU.Lay0U (bv_unsigned sp)) (fun _ => PMX.pm_staticsx)).
    - intros sp _. exact (TopGlueU.Lay0U_drv (bv_unsigned sp)).
    - exact LIBU.
    - intros sp _. exact TopGlueU.pm_exit_ok.
    - intros sp _. exact (TopGlueU.Lay0U_credit (bv_unsigned sp)).
  Qed.
End Lay.
End FPX_1.
End PmXubsanTgtLay.
