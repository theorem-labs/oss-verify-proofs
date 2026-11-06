(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgNum. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgNum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
(* [comment removed for export] *)

Module BgNumCertIS_A0.
Lemma cut : cut_ok BNI MS (BgNum.BgNumT.ce MS BNI) (BgNum.XN BNI) (arm_of BNI) 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertIS_A0.

Module BgNumCertIS_A1.
Lemma cut : cut_ok BNI MS (BgNum.BgNumT.ce MS BNI) (BgNum.XN BNI) (arm_of BNI) 1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertIS_A1.

Module BgNumCertIS_A2.
Lemma cut : cut_ok BNI MS (BgNum.BgNumT.ce MS BNI) (BgNum.XN BNI) (arm_of BNI) 2 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertIS_A2.

Module BgNumCertIS_A3.
Lemma cut : cut_ok BNI MS (BgNum.BgNumT.ce MS BNI) (BgNum.XN BNI) (arm_of BNI) 3 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertIS_A3.

Module BgNumCertIS_A4.
Lemma cut : cut_ok BNI MS (BgNum.BgNumT.ce MS BNI) (BgNum.XN BNI) (arm_of BNI) 4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertIS_A4.

Module BgNumCertUS_A0.
Lemma cut : cut_ok BNU MS (BgNum.BgNumT.ce MS BNU) (BgNum.XN BNU) (arm_of BNU) 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertUS_A0.

Module BgNumCertUS_A1.
Lemma cut : cut_ok BNU MS (BgNum.BgNumT.ce MS BNU) (BgNum.XN BNU) (arm_of BNU) 1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertUS_A1.

Module BgNumCertUS_A2.
Lemma cut : cut_ok BNU MS (BgNum.BgNumT.ce MS BNU) (BgNum.XN BNU) (arm_of BNU) 2 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertUS_A2.

Module BgNumCertUS_A3.
Lemma cut : cut_ok BNU MS (BgNum.BgNumT.ce MS BNU) (BgNum.XN BNU) (arm_of BNU) 3 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertUS_A3.

Module BgNumCertUS_A4.
Lemma cut : cut_ok BNU MS (BgNum.BgNumT.ce MS BNU) (BgNum.XN BNU) (arm_of BNU) 4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertUS_A4.
