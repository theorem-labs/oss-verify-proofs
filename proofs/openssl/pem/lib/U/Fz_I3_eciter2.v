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

Lemma eclear_iter_5 : eclear_iter_stmt 5 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 5%nat. Qed.
Lemma eclear_iter_6 : eclear_iter_stmt 6 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 6%nat. Qed.
Lemma eclear_iter_7 : eclear_iter_stmt 7 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 7%nat. Qed.
Lemma eclear_iter_8 : eclear_iter_stmt 8 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 8%nat. Qed.
Lemma eclear_iter_9 : eclear_iter_stmt 9 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 9%nat. Qed.
Lemma eclear_iter_10 : eclear_iter_stmt 10 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 10%nat. Qed.
End WithCeiling0.
