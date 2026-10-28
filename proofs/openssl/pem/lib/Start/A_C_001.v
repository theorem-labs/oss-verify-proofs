(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_HS_000 A_HS_001.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition A_plan_001 : plan := PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 283)) (ELit 4096) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar 283)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XMemIsZero [] (PRun [] (PX XMemset [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 348)) (ELit 4096) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar 348)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 349)) (ELit 4096) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar 349)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PSys YMunmap (PSplit (EVar 6) 10 (PRun [0x1dede0] (PFresh 10 12 (Some e_pgsp) (PRun [0x1c45a8] (PDiamondT 0x1c47d4 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PFact (KWr (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PFact (KZero (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PX XMemset [] (PFact (KRange (esub (eaddz (escale 16 (EVar 6)) 3935) (escale 4096 (EVar 382))) 0 4095) (PFact (KRange (EVar 382) 0 1) (PHandoff 0))))))))))) (PRun [0x1dede0] (PFresh 10 12 (Some e_pgsp) (PRun [0x1c45a8] (PDiamondT 0x1c47d4 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PFact (KWr (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PFact (KZero (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PX XMemset [] (PFact (KRange (esub (eaddz (escale 16 (EVar 6)) 3935) (escale 4096 (EVar 382))) 0 4095) (PFact (KRange (EVar 382) 0 1) (PHandoff 0))))))))))))))))))))))))))))))))))))).
Definition A_ranges_001 : list (Z * nat) := [(0x19c0f0, 29%nat); (0x19c214, 10%nat); (0x19c320, 23%nat); (0x19d300, 24%nat); (0x19d3f0, 13%nat); (0x1ab8dc, 15%nat); (0x1ac5ec, 5%nat); (0x1b3d2c, 35%nat); (0x1c1910, 5%nat); (0x1c2364, 55%nat); (0x1c2508, 29%nat); (0x1c4548, 43%nat); (0x1c46a8, 9%nat); (0x1c4778, 39%nat); (0x1c48b0, 18%nat); (0x1c4a44, 31%nat); (0x1c4ed0, 77%nat); (0x1c5034, 20%nat); (0x1c56b4, 29%nat); (0x1ca810, 17%nat); (0x1cca74, 7%nat); (0x1ccdec, 15%nat); (0x1cd0bc, 26%nat); (0x1cd560, 86%nat); (0x1cd764, 22%nat); (0x1cd868, 6%nat); (0x1cd954, 63%nat); (0x1cdbb4, 15%nat); (0x1cdc94, 28%nat); (0x1ceef4, 78%nat); (0x1cf78c, 16%nat); (0x1d1568, 30%nat); (0x1d4e08, 13%nat); (0x1d53b4, 43%nat); (0x1d5748, 18%nat); (0x1d6e4c, 60%nat); (0x1d6fcc, 30%nat); (0x1d7b28, 21%nat); (0x1d7c78, 14%nat); (0x1daa44, 30%nat); (0x1dab14, 75%nat); (0x1dacdc, 38%nat); (0x1dae00, 33%nat); (0x1dc564, 21%nat); (0x1dc774, 134%nat); (0x1dca24, 13%nat); (0x1dd66c, 50%nat); (0x1ded48, 44%nat); (0x1dee64, 12%nat); (0x1df048, 36%nat); (0x1df2bc, 65%nat); (0x1df43c, 56%nat); (0x1dfbc8, 117%nat); (0x51b444, 111%nat); (0x52690c, 66%nat); (0x5275c4, 13%nat); (0x529430, 11%nat); (0x52a57c, 17%nat)].
Definition A_IT_001 : itab := mk_itab_ranges A_SEGS A_ranges_001.
Lemma A_IT_001_ok : itab_sound A_SEGS A_IT_001.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition A_shape_001 : shape := SCase (EVar 6) 10 (SHole 0) (SHole 0).

Lemma A_cert_001 :
  check A_SEGS A_IT_001 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HS_001) 0%nat 400000%nat 40000%nat None A_HS_000 A_plan_001
  = COk A_shape_001.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_001)). Qed.
