(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_HS_005 A_HS_006.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition A_plan_006 : plan := PBump 124 (PExt 66 [ELit 1219; ELit 1] (PRun [] (PBump 172 (PMmap PSpin (PRename [(172, 60)]%nat (PShDisj (escale 4096 (EVar 60)) (ELit 4096) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar 60)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PExt 63 [escale 4096 (EVar 60)] (PRun [] (PX XMemset [] (PRun [0x1a94ec] (PExt 66 [ELit 2839; ELit 2] (PGcKeep [(ELit 65536, ELit 12122784); (ELit 12203373, ELit 141971); (ELit 2147446784, ELit 41492); (ELit 2147446784, ELit 268435456); (ELit 2147595320, ELit 8); (ELit 2148965872, ELit 8264); (ELit 2148993344, ELit 136); (ELit 2147557744, ELit 268324496); (escale 4096 (EVar 26), ELit 0)] (PGcRangeAuto (PCompact (PHandoff 0)))))))))))))))).
Definition A_ranges_006 : list (Z * nat) := [(0x1a94d0, 30%nat); (0x1a961c, 6%nat); (0x1a9748, 13%nat); (0x1a987c, 63%nat); (0x1a9a60, 35%nat); (0x1a9b6c, 19%nat); (0x1ab168, 90%nat); (0x1ab308, 116%nat); (0x1ab588, 54%nat); (0x1ab6d0, 108%nat); (0x1aba2c, 72%nat); (0x1c4534, 48%nat); (0x1c46a8, 9%nat); (0x1c4778, 35%nat); (0x1c48b0, 18%nat); (0x1c9900, 10%nat); (0x1cacec, 6%nat); (0x1cf6c8, 74%nat); (0x1d1568, 30%nat); (0x1d5748, 18%nat); (0x1d6e4c, 60%nat); (0x1d6fcc, 30%nat); (0x1d7b28, 21%nat); (0x1d7c78, 14%nat); (0x52690c, 66%nat)].
Definition A_IT_006 : itab := mk_itab_ranges A_SEGS A_ranges_006.
Lemma A_IT_006_ok : itab_sound A_SEGS A_IT_006.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition A_shape_006 : shape := SHole 0.

Lemma A_cert_006 :
  check A_SEGS A_IT_006 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HS_006) 0%nat 400000%nat 40000%nat None A_HS_005 A_plan_006
  = COk A_shape_006.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_006)). Qed.
