(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface RT_rep RT_closed.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import BnRepDefs LibaA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaIface HxaFinal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem init_cps_RTA : init_cps RTA (LIBA RTA).
Proof. exact (init_cps_A RTA (rc_facts RTA rta_contracts_all) rta_contracts_all rta_live_pos). Qed.
