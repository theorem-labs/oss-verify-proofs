(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_HS_002 A_HS_003.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition A_plan_003 : plan := PRun [] (PX XIMemset [] (PRun [] (PX XIMemset [] (PCase2 (esub (eaddz (escale 16 (EVar 6)) 3935) (escale 4096 (EVar 382))) 4030 (PRun [0x1a91ec] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [0x1a94ec] (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 28; 29; 30; 31]%nat (PJoin (ELit 0) 10713200 4%nat (PJoin (ELit 0) 7930832 4%nat (PJoin (escale 4096 (EVar 491)) 16 8%nat (PHandoff 0))))))))))))))))))))))))) (PRun [0x1a91ec] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [0x1a94ec] (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 28; 29; 30; 31]%nat (PJoin (ELit 0) 10713200 4%nat (PJoin (ELit 0) 7930832 4%nat (PJoin (escale 4096 (EVar 491)) 16 8%nat (PHandoff 0))))))))))))))))))))))))))))).
Definition A_ranges_003 : list (Z * nat) := [(0x1a90b4, 112%nat); (0x1a92e0, 53%nat); (0x1a9434, 49%nat); (0x1aa49c, 18%nat); (0x1ac448, 55%nat); (0x1c56b4, 11%nat); (0x1c9900, 10%nat); (0x1ca58c, 11%nat); (0x1ca774, 19%nat); (0x1caaf0, 13%nat); (0x1cb598, 50%nat); (0x1cb6c0, 18%nat); (0x1cc4bc, 35%nat); (0x1cd0bc, 12%nat); (0x1cd280, 48%nat); (0x1cf6c8, 26%nat); (0x1cf794, 14%nat); (0x1d1568, 15%nat); (0x1d1c78, 5%nat); (0x1d1cc0, 5%nat); (0x1d4e08, 13%nat); (0x1d4e84, 28%nat); (0x1d4f38, 17%nat); (0x1d4fd8, 11%nat); (0x1d5748, 15%nat); (0x1d6e4c, 60%nat); (0x1d6fcc, 30%nat); (0x1d7384, 58%nat); (0x1d7b28, 21%nat); (0x1d7c78, 14%nat); (0x1d9ee8, 36%nat); (0x1da124, 11%nat); (0x1da180, 68%nat); (0x1da3d0, 19%nat); (0x1e29e8, 107%nat); (0x1e2c18, 7%nat); (0x1e34f4, 42%nat); (0x1e4cfc, 22%nat); (0x1e4fe4, 85%nat); (0x1e517c, 71%nat); (0x1e5778, 91%nat); (0x1e5968, 29%nat); (0x1e5a10, 37%nat); (0x1e5fcc, 35%nat); (0x1e60ac, 18%nat); (0x1f28e0, 79%nat); (0x1f3048, 12%nat); (0x51b3b0, 18%nat); (0x51c400, 21%nat); (0x51c4a8, 27%nat); (0x51c570, 17%nat); (0x51c61c, 40%nat); (0x51c9ec, 53%nat); (0x51cc2c, 162%nat); (0x51cfc8, 155%nat); (0x51d2ac, 105%nat); (0x51fa24, 63%nat); (0x5272a0, 7%nat); (0x527498, 5%nat); (0x527528, 7%nat); (0x527630, 33%nat); (0x529430, 11%nat); (0x52ac50, 24%nat)].
Definition A_IT_003 : itab := mk_itab_ranges A_SEGS A_ranges_003.
Lemma A_IT_003_ok : itab_sound A_SEGS A_IT_003.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition A_shape_003 : shape := SHole 0.

Lemma A_cert_003 :
  check A_SEGS A_IT_003 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HS_003) 0%nat 400000%nat 40000%nat None A_HS_002 A_plan_003
  = COk A_shape_003.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_003)). Qed.
