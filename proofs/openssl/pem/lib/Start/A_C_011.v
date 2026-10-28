(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_HS_010 A_HS_011.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition A_plan_011 : plan := PRun [0x1c45a8] (PDiamondT 0x1c47d4 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PRun [0x1f2b8c] (PGcKeep [(escale 4096 (EVar 25), ELit 0); (escale 4096 (EVar 15), ELit 0); (ELit 0, ELit 5431296); (ELit 5433296, ELit 287); (ELit 5915688, ELit 623); (ELit 5918912, ELit 543); (ELit 5921600, ELit 447); (ELit 5923960, ELit 431); (ELit 5928256, ELit 879); (ELit 5938856, ELit 319); (ELit 5940968, ELit 782279); (ELit 6723328, ELit 495); (ELit 6726264, ELit 511); (ELit 6734620, ELit 267); (ELit 6736568, ELit 267); (ELit 6739864, ELit 295); (ELit 7269666, ELit 256); (ELit 7325000, ELit 287); (ELit 7333248, ELit 620); (ELit 7334240, ELit 256); (ELit 7596424, ELit 283); (ELit 10713200, ELit 4); (ELit 7930832, ELit 4); (ELit 11856408, ELit 151); (ELit 12120336, ELit 67376); (ELit 12187712, ELit 336); (ELit 12205568, ELit 132099); (ELit 12338536, ELit 263); (ELit 12340824, ELit 8); (ELit 12341784, ELit 263); (ELit 12345344, ELit 4611686018427387904)] (PGcRangeAuto (PCompact (PHandoff 0)))))))).
Definition A_ranges_011 : list (Z * nat) := [(0x199a5c, 34%nat); (0x1a9ba4, 81%nat); (0x1aa4d4, 10%nat); (0x1aabf0, 41%nat); (0x1aacf8, 110%nat); (0x1ab0d0, 17%nat); (0x1c4548, 27%nat); (0x1c4778, 9%nat); (0x1c47cc, 14%nat); (0x1c48b0, 18%nat); (0x1dec94, 12%nat); (0x1decf4, 5%nat); (0x1f2b84, 5%nat); (0x1f3068, 7%nat); (0x51a880, 13%nat); (0x51a938, 8%nat); (0x52690c, 66%nat)].
Definition A_IT_011 : itab := mk_itab_ranges A_SEGS A_ranges_011.
Lemma A_IT_011_ok : itab_sound A_SEGS A_IT_011.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition A_shape_011 : shape := SHole 0.

Lemma A_cert_011 :
  check A_SEGS A_IT_011 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HS_011) 0%nat 400000%nat 40000%nat None A_HS_010 A_plan_011
  = COk A_shape_011.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_011)). Qed.
