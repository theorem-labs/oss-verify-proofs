(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GaCommon AzStrResizeT AzStrResizeA GaW16 GaNum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
(* [comment removed for export] *)

Module GaNumCertIS_A0.
Lemma cut : cut_ok BNI MS (GaNumT.ce MS BNI) (GaNum.XN BNI) (arm_of BNI) 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertIS_A0.

Module GaNumCertIS_A1.
Lemma cut : cut_ok BNI MS (GaNumT.ce MS BNI) (GaNum.XN BNI) (arm_of BNI) 1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertIS_A1.

Module GaNumCertIS_A2.
Lemma cut : cut_ok BNI MS (GaNumT.ce MS BNI) (GaNum.XN BNI) (arm_of BNI) 2 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertIS_A2.

Module GaNumCertIS_A3.
Lemma cut : cut_ok BNI MS (GaNumT.ce MS BNI) (GaNum.XN BNI) (arm_of BNI) 3 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertIS_A3.

Module GaNumCertIS_A4.
Lemma cut : cut_ok BNI MS (GaNumT.ce MS BNI) (GaNum.XN BNI) (arm_of BNI) 4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertIS_A4.

Module GaNumCertUS_A0.
Lemma cut : cut_ok BNU MS (GaNumT.ce MS BNU) (GaNum.XN BNU) (arm_of BNU) 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertUS_A0.

Module GaNumCertUS_A1.
Lemma cut : cut_ok BNU MS (GaNumT.ce MS BNU) (GaNum.XN BNU) (arm_of BNU) 1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertUS_A1.

Module GaNumCertUS_A2.
Lemma cut : cut_ok BNU MS (GaNumT.ce MS BNU) (GaNum.XN BNU) (arm_of BNU) 2 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertUS_A2.

Module GaNumCertUS_A3.
Lemma cut : cut_ok BNU MS (GaNumT.ce MS BNU) (GaNum.XN BNU) (arm_of BNU) 3 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertUS_A3.

Module GaNumCertUS_A4.
Lemma cut : cut_ok BNU MS (GaNumT.ce MS BNU) (GaNum.XN BNU) (arm_of BNU) 4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertUS_A4.
