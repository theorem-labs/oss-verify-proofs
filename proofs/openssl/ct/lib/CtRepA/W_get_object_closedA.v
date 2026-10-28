(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApState ApLogic ApErr ApParse.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA ImplA UnwindA EdgesA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface I_strcpyA W_err_newA W_err_set_debugA W_err_vsetA W_get_objectA W_get_object_walkA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).

(* [comment removed for export] *)
Lemma ASN1_get_object_closedA : strcpy_icontract RT -> ASN1_get_object_specA.
Proof.
  intros STRCPY. apply ASN1_get_object_walkA.
  - exact ERR_new_walkA.
  - intros rs RF RN bo0.
    destruct (lit_okA_auto A_ASN1_LIB_C_A 23 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_okA_auto A_ASN1_GET_OBJECT_FN_A 16 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    rewrite <- RF in LF. rewrite <- RN in LN.
    exact (ERR_set_debug_walkA STRCPY rs _ _ bo0 fs fk ns nk LF LN).
  - intros rs lib reason. apply (@ERR_set_error_closedA AR UK BE).
Qed.

End WithRT.
