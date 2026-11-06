(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA AShadow ARt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg A_amemmove_stmt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AHeapR AHeapL AHeapHIA AW_AMemmoveT.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_AMemmoveS () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.AHeap.ACeil.ACEIL"; "OSSVerify.KrLib.AHeap.AHeapHIA.b12_T"; "OSSVerify.KrLib.AHeap.AHeapHIA.mod_die_T"; "OSSVerify.KrLib.AHeap.AFreePost.freeH_T"; "OSSVerify.KrLib.A.A_amemmove_stmt.amemmove_stmtA"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.AHeap.AHeapR.R0"; "OSSVerify.KrLib.AHeap.AHeapHIA.artA_i"; "OSSVerify.KrLib.A.A_amemmove_stmt.A_ASAN_MEMMOVE"].


Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Theorem amemmove_stmt_i : ltac2:(CDefT.buildp (gd_tbl_AW_AMemmoveS ()) "PSTKLO,$0.PSTKLO_OK,(1.(2.VhAR,)R1.)PB12,(3.VhAR,)PMOD_DIE,$4.PFH,(5.VhAR,R4.)(6.$7.(8.VhAR,R5.)(9.VhAR,R5.R4.R3.R2.R1.)$:.)")
(* [comment removed for export] *).
Proof.
  intros STKLO STKLO_OK B12 MOD_DIE FH. unfold amemmove_stmtA, A_ASAN_MEMMOVE.
  intros until ss. intros HM1 ARR BS LEN LENS OBJ OBJS ST LO SPL CRS MI DISJ DISJS TOP8 TOP8S N40 CW SPT E0 E1 E2.
  eapply (amemmove_i STKLO); eassumption.
Qed.
End ARUN_1.
