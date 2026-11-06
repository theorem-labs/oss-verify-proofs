(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec AsanAcct AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanSort AsanSortSound AsanSortBridge B_PlanImage B_Atable.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import RT_iface XR_rehash_k XR_isort.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A_ISORT : Z := 0x1bc1b4.

Theorem A_isort_contract : HSNS.isort_contract B_SEGS A_ISORT.
Proof. exact (HSB.isort_contract_of_walk B_SEGS A_ISORT A_seg_below B_t_segs_wx xr_isort_spec). Qed.
