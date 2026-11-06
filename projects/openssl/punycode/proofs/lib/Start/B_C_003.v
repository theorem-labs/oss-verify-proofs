(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs B_HS_002 B_HS_003.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition B_plan_003 : plan := PRun [] (PX XIMemset [] (PRun [] (PX XIMemset [] (PCase2 (esub (eaddz (escale 16 (EVar 6)) 3935) (escale 4096 (EVar 382))) 4030 (PRun [0x1a4158] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (ELit 65536) (ELit 12505088) (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (ELit 65536) (ELit 12505088) (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (ELit 65536) (ELit 12505088) (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [0x1a4458] (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 28; 29; 30; 31]%nat (PJoin (ELit 0) 11663372 4%nat (PJoin (ELit 0) 7891516 4%nat (PJoin (escale 4096 (EVar 491)) 16 8%nat (PHandoff 0))))))))))))))))))))))))) (PRun [0x1a4158] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (ELit 65536) (ELit 12505088) (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (ELit 65536) (ELit 12505088) (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (ELit 65536) (ELit 12505088) (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [0x1a4458] (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 28; 29; 30; 31]%nat (PJoin (ELit 0) 11663372 4%nat (PJoin (ELit 0) 7891516 4%nat (PJoin (escale 4096 (EVar 491)) 16 8%nat (PHandoff 0))))))))))))))))))))))))))))).
Definition B_ranges_003 : list (Z * nat) := [(0x1a4020, 112%nat); (0x1a424c, 53%nat); (0x1a43a0, 49%nat); (0x1a5408, 18%nat); (0x1a73b4, 55%nat); (0x1c0620, 11%nat); (0x1c486c, 10%nat); (0x1c54f8, 11%nat); (0x1c56e0, 19%nat); (0x1c5a5c, 13%nat); (0x1c6504, 50%nat); (0x1c662c, 18%nat); (0x1c7428, 35%nat); (0x1c8028, 12%nat); (0x1c81ec, 48%nat); (0x1ca634, 26%nat); (0x1ca700, 14%nat); (0x1cc4d4, 15%nat); (0x1ccbe4, 5%nat); (0x1ccc2c, 5%nat); (0x1cfd74, 13%nat); (0x1cfdf0, 28%nat); (0x1cfea4, 17%nat); (0x1cff44, 11%nat); (0x1d06b4, 15%nat); (0x1d1db8, 60%nat); (0x1d1f38, 30%nat); (0x1d22f0, 58%nat); (0x1d2a94, 21%nat); (0x1d2be4, 14%nat); (0x1d4e54, 36%nat); (0x1d5090, 11%nat); (0x1d50ec, 68%nat); (0x1d533c, 19%nat); (0x1dd954, 107%nat); (0x1ddb84, 7%nat); (0x1de460, 42%nat); (0x1dfc68, 22%nat); (0x1dff50, 85%nat); (0x1e00e8, 71%nat); (0x1e06e4, 91%nat); (0x1e08d4, 29%nat); (0x1e097c, 37%nat); (0x1e0f38, 35%nat); (0x1e1018, 18%nat); (0x1ed84c, 79%nat); (0x1edfb4, 12%nat); (0x5581d4, 18%nat); (0x559224, 21%nat); (0x5592cc, 27%nat); (0x559394, 17%nat); (0x559440, 40%nat); (0x559810, 53%nat); (0x559a50, 162%nat); (0x559dec, 155%nat); (0x55a0d0, 105%nat); (0x55c848, 63%nat); (0x5640c4, 7%nat); (0x5642bc, 5%nat); (0x56434c, 7%nat); (0x564454, 33%nat); (0x566254, 11%nat); (0x567a74, 24%nat)].
Definition B_IT_003 : itab := mk_itab_ranges B_SEGS B_ranges_003.
Lemma B_IT_003_ok : itab_sound B_SEGS B_IT_003.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition B_shape_003 : shape := SHole 0.

Lemma B_cert_003 :
  check B_SEGS B_IT_003 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HS_003) 0%nat 400000%nat 40000%nat None B_HS_002 B_plan_003
  = COk B_shape_003.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_003)). Qed.
