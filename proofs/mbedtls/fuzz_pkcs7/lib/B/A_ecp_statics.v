(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Image MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals A_mpi_stmtA_sz A_ecp_stmtA A_ecp_defs.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_ecp_statics () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.is_sw"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.grp_imgA"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.grp_sw"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_CA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_ONE"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.grp_mx"].


Lemma A_curve_statics : forall m id, mem_inv asegs m -> 1 <= id <= 13 -> curve_statics asegs (A_CA id) A_ONE id m.
Proof.
  intros m id MI Hid.
  assert (C : id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7 \/ id = 8 \/ id = 9 \/ id = 10 \/ id = 11 \/ id = 12 \/ id = 13) by lia.
  Ltac one MI := apply static_limbs_image; [exact MI| vm_compute; reflexivity| reflexivity| reflexivity| cbn; lia| cbn; lia].
  destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
    unfold curve_statics, A_ONE; cbn [A_CA ca_P ca_A ca_B ca_GX ca_GY ca_N cP cA cB cGX cGY cN has_A is_sw];
    (split; [one MI|]); (split; [intros HA; first [discriminate HA| one MI]|]); (split; [intros HS; first [discriminate HS| split; [one MI| split; one MI]]|]); (split; one MI).
Qed.

(* [comment removed for export] *)
Lemma A_grp_sw_imgA : ltac2:(CDefT.buildp (gd_tbl_A_ecp_statics ()) "Pid,$0.PA,$0.Pidpad,(1.&40.)PpP,(1.&40.)PpA,(1.&40.)PpB,(1.&40.)PpX,(1.&40.)PpY,(1.&40.)PpZ,(1.&40.)PpN,(1.&40.)Phpad,(1.&40.)P,(2.(3.+1.R;.)(3.R;.+=.))P,(4.$5.(6.R<.)$7.)(8.(9.R=.(:.R=.)$;.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros id A idpad pP pA pB pX pY pZ pN hpad Hid SW.
  assert (C : id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7 \/ id = 8 \/ id = 9 \/ id = 10 \/ id = 11 \/ id = 12 \/ id = 13) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]; try discriminate SW;
    unfold grp_imgA, grp_mpds, pt_mpds, grp_sw; cbn [has_A g_P g_A g_B g_G g_N pt_X pt_Y pt_Z app];
    repeat (apply Forall_cons; [unfold mpd_imgA, smpd, mpd_init; cbn [md_own md_p md_n]; intros E; first [discriminate E | vm_compute; reflexivity]|]); apply Forall_nil.
Qed.

(* [comment removed for export] *)
Lemma A_grp_mx_imgA : ltac2:(CDefT.buildp (gd_tbl_A_ecp_statics ()) "Pid,$0.PA,$0.Pidpad,(1.&40.)PpP,(1.&40.)PpA,(1.&40.)PpB,(1.&40.)PpX,(1.&40.)PpY,(1.&40.)PpZ,(1.&40.)PpN,(1.&40.)Phpad,(1.&40.)PPA,$0.PPX,$0.PPZ,$0.PwA,(1.&40.)PwX,(1.&40.)PwZ,(1.&40.)P,(<.(4.$0.R11.+9.)(4.$0.R11.+=.))(8.(=.R12.(:.R12.)R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros id A idpad pP pA pB pX pY pZ pN hpad PA PX PZ wA wX wZ [-> | ->];
    unfold grp_imgA, grp_mpds, pt_mpds, grp_mx, grp_mxi; cbn [g_P g_A g_B g_G g_N pt_X pt_Y pt_Z app];
    repeat (apply Forall_cons; [unfold mpd_imgA, smpd, mpd_init, heap1; cbn [md_own md_p md_n]; intros E; first [discriminate E | vm_compute; reflexivity]|]); apply Forall_nil.
Qed.
