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

Module BgNumCertIL1_A0.
Lemma cut : cut_ok BNI ML (BgNum.BgNumT.ceL1 BNI) (BgNum.XN1 BNI) (arm_ofL1 BNI) 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertIL1_A0.

Module BgNumCertIL1_A1.
Lemma cut : cut_ok BNI ML (BgNum.BgNumT.ceL1 BNI) (BgNum.XN1 BNI) (arm_ofL1 BNI) 1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertIL1_A1.

Module BgNumCertIL1_A2.
Lemma cut : cut_ok BNI ML (BgNum.BgNumT.ceL1 BNI) (BgNum.XN1 BNI) (arm_ofL1 BNI) 2 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertIL1_A2.

Module BgNumCertIL1_A3.
Lemma cut : cut_ok BNI ML (BgNum.BgNumT.ceL1 BNI) (BgNum.XN1 BNI) (arm_ofL1 BNI) 3 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertIL1_A3.

Module BgNumCertIL1_A4.
Lemma cut : cut_ok BNI ML (BgNum.BgNumT.ceL1 BNI) (BgNum.XN1 BNI) (arm_ofL1 BNI) 4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertIL1_A4.

Module BgNumCertUL1_A0.
Lemma cut : cut_ok BNU ML (BgNum.BgNumT.ceL1 BNU) (BgNum.XN1 BNU) (arm_ofL1 BNU) 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertUL1_A0.

Module BgNumCertUL1_A1.
Lemma cut : cut_ok BNU ML (BgNum.BgNumT.ceL1 BNU) (BgNum.XN1 BNU) (arm_ofL1 BNU) 1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertUL1_A1.

Module BgNumCertUL1_A2.
Lemma cut : cut_ok BNU ML (BgNum.BgNumT.ceL1 BNU) (BgNum.XN1 BNU) (arm_ofL1 BNU) 2 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertUL1_A2.

Module BgNumCertUL1_A3.
Lemma cut : cut_ok BNU ML (BgNum.BgNumT.ceL1 BNU) (BgNum.XN1 BNU) (arm_ofL1 BNU) 3 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertUL1_A3.

Module BgNumCertUL1_A4.
Lemma cut : cut_ok BNU ML (BgNum.BgNumT.ceL1 BNU) (BgNum.XN1 BNU) (arm_ofL1 BNU) 4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
(* [comment removed for export] *)
End BgNumCertUL1_A4.
