(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import A_Chain.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import TopA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

Lemma hs_ok_3 : hs_all_ok (inst A_HSm V_F (ELit 3)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
