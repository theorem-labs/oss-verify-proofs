(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_free. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_I3_eciter.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma eclear_iter_11 : eclear_iter_stmt 11 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 11%nat. Qed.
Lemma eclear_iter_12 : eclear_iter_stmt 12 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 12%nat. Qed.
Lemma eclear_iter_13 : eclear_iter_stmt 13 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 13%nat. Qed.
Lemma eclear_iter_14 : eclear_iter_stmt 14 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 14%nat. Qed.
Lemma eclear_iter_15 : eclear_iter_stmt 15 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 15%nat. Qed.
End WithCeiling0.
