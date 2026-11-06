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

Module GaNumCertIL1_A0.
Lemma cut : cut_ok BNI ML (GaNumT.ceL1 BNI) (GaNum.XN1 BNI) (arm_ofL1 BNI) 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertIL1_A0.

Module GaNumCertIL1_A1.
Lemma cut : cut_ok BNI ML (GaNumT.ceL1 BNI) (GaNum.XN1 BNI) (arm_ofL1 BNI) 1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertIL1_A1.

Module GaNumCertIL1_A2.
Lemma cut : cut_ok BNI ML (GaNumT.ceL1 BNI) (GaNum.XN1 BNI) (arm_ofL1 BNI) 2 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertIL1_A2.

Module GaNumCertIL1_A3.
Lemma cut : cut_ok BNI ML (GaNumT.ceL1 BNI) (GaNum.XN1 BNI) (arm_ofL1 BNI) 3 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertIL1_A3.

Module GaNumCertIL1_A4.
Lemma cut : cut_ok BNI ML (GaNumT.ceL1 BNI) (GaNum.XN1 BNI) (arm_ofL1 BNI) 4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertIL1_A4.

Module GaNumCertUL1_A0.
Lemma cut : cut_ok BNU ML (GaNumT.ceL1 BNU) (GaNum.XN1 BNU) (arm_ofL1 BNU) 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertUL1_A0.

Module GaNumCertUL1_A1.
Lemma cut : cut_ok BNU ML (GaNumT.ceL1 BNU) (GaNum.XN1 BNU) (arm_ofL1 BNU) 1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertUL1_A1.

Module GaNumCertUL1_A2.
Lemma cut : cut_ok BNU ML (GaNumT.ceL1 BNU) (GaNum.XN1 BNU) (arm_ofL1 BNU) 2 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertUL1_A2.

Module GaNumCertUL1_A3.
Lemma cut : cut_ok BNU ML (GaNumT.ceL1 BNU) (GaNum.XN1 BNU) (arm_ofL1 BNU) 3 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertUL1_A3.

Module GaNumCertUL1_A4.
Lemma cut : cut_ok BNU ML (GaNumT.ceL1 BNU) (GaNum.XN1 BNU) (arm_ofL1 BNU) 4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End GaNumCertUL1_A4.
