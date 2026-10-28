(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AHeapR AW_MmapDie AW_MapOrDie AW_MallocSecS AW_ModDieWalk AHeapHIA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Theorem mod_die_walk : mod_die_T.
Proof.
  unfold mod_die_T. intros CS gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 ra SP0 F fc m0 mm addr size lo0 fr
    CSOK AB SZ FR [SEAL DY] ST LOIMG SPL SPH MU WM MI SCS.
  eapply (mapordie_post_die AL0 AL0_img AL0_wf CS CSOK gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 ra SP0 F fc m0 mm addr size lo0 fr);
    eassumption.
Qed.
End ARUN_1.
(* [comment removed for export] *)
