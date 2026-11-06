(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState Arr Asn1Aux CellsX HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM AHeapR.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Export AH0Spec0.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AH0Spec () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.BHeap.AH0Spec0.bp_sp0"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.BHeap.AHeapR.hok"; "OSSVerify.KrLib.BHeap.AH0Spec0.h0_of"; "OSSVerify.KrLib.BHeap.AHeapR.HM_i"; "OSSVerify.KrLib.BHeap.AHeapR.HS"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.BHeap.AHeapR.HK_i"; "OSSVerify.KrLib.BHeap.AModel.h_havol"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.BHeap.AModelX.hfr"; "OSSVerify.KrLib.BHeap.AModel.r_mapped_user"; "OSSVerify.KrLib.BHeap.AModel.h_reg"; "OSSVerify.KrLib.BHeap.AHeapR.htop_i"; "OSSVerify.KrLib.BHeap.AHeapR.hstkhi_i"; "OSSVerify.KrLib.BHeap.AH0Spec0.bp_stkhi"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
Section Goal.
  Variable STKLO : Z.

  Definition h0_goal (bp : boot_params) (mem : mem) (md : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_AH0Spec ()) "(0.(1.$2.(3.(4.O3.)(5.+2.+17.))VSTKLO,)(6.(7.VhAR,VSTKLO,(8.O3.))LHOK,(7.VhAR,VSTKLO,(8.O3.))(0.(9.VhAR,VSTKLO,(:.VhAR,VSTKLO,(8.O3.)R1.)(;.$<.)(;.$<.)O2.)(0.(=.VhAR,VSTKLO,(:.VhAR,VSTKLO,(8.O3.)R1.)O1.)(0.(1.$2.(>.(8.O3.))=)(0.(?.(10.(8.O3.))=)(0.Pc,$2.(1.$2.(11.(12.(8.O3.)R1.))=)(0.(1.$2.(13.VhAR,VSTKLO,(:.VhAR,VSTKLO,(8.O3.)R1.))(3.(4.O3.)+30.))(1.$2.(14.VhAR,VSTKLO,(:.VhAR,VSTKLO,(8.O3.)R1.))(15.O3.))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  End Goal.

End ARUN_1.
