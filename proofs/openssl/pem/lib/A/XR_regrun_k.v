(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec AsanAcct AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanRegModel AsanRegStmt AsanRegContract AsanRegBridge A_RegConsts A_PlanImage A_Atable.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import RT_ibase XR_rehash_k XR_regrun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Theorem A_regrun_contract : RGK.regrun_contract A_SEGS A_RGC.
Proof. exact (RGB.regrun_contract_of_walk A_SEGS A_RGC A_seg_below A_t_segs_wx (eq_refl true) xr_regrun_spec). Qed.
