(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs B_HS_002 B_HS_003.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition B_plan_003 : plan := PRun [] (PX XIMemset [] (PRun [] (PX XIMemset [] (PCase2 (esub (eaddz (escale 16 (EVar 6)) 3935) (escale 4096 (EVar 382))) 4030 (PRun [0x1a41a4] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [0x1a44a4] (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 28; 29; 30; 31]%nat (PJoin (ELit 0) 9007720 4%nat (PJoin (ELit 0) 9241720 4%nat (PJoin (escale 4096 (EVar 491)) 16 8%nat (PHandoff 0))))))))))))))))))))))))) (PRun [0x1a41a4] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [0x1a44a4] (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 28; 29; 30; 31]%nat (PJoin (ELit 0) 9007720 4%nat (PJoin (ELit 0) 9241720 4%nat (PJoin (escale 4096 (EVar 491)) 16 8%nat (PHandoff 0))))))))))))))))))))))))))))).
Definition B_ranges_003 : list (Z * nat) := [(0x1a406c, 112%nat); (0x1a4298, 53%nat); (0x1a43ec, 49%nat); (0x1a5454, 18%nat); (0x1a7400, 55%nat); (0x1c066c, 11%nat); (0x1c48b8, 10%nat); (0x1c5544, 11%nat); (0x1c572c, 19%nat); (0x1c5aa8, 13%nat); (0x1c6550, 50%nat); (0x1c6678, 18%nat); (0x1c7474, 35%nat); (0x1c8074, 12%nat); (0x1c8238, 48%nat); (0x1ca680, 26%nat); (0x1ca74c, 14%nat); (0x1cc520, 15%nat); (0x1ccc30, 5%nat); (0x1ccc78, 5%nat); (0x1cfdc0, 13%nat); (0x1cfe3c, 28%nat); (0x1cfef0, 17%nat); (0x1cff90, 11%nat); (0x1d0700, 15%nat); (0x1d1e04, 60%nat); (0x1d1f84, 30%nat); (0x1d233c, 58%nat); (0x1d2ae0, 21%nat); (0x1d2c30, 14%nat); (0x1d4ea0, 36%nat); (0x1d50dc, 11%nat); (0x1d5138, 68%nat); (0x1d5388, 19%nat); (0x1dd9a0, 107%nat); (0x1ddbd0, 7%nat); (0x1de4ac, 42%nat); (0x1dfcb4, 22%nat); (0x1dff9c, 85%nat); (0x1e0134, 71%nat); (0x1e0730, 91%nat); (0x1e0920, 29%nat); (0x1e09c8, 37%nat); (0x1e0f84, 35%nat); (0x1e1064, 18%nat); (0x1ed898, 79%nat); (0x1ee000, 12%nat); (0x553aac, 18%nat); (0x554afc, 21%nat); (0x554ba4, 27%nat); (0x554c6c, 17%nat); (0x554d18, 40%nat); (0x5550e8, 53%nat); (0x555328, 162%nat); (0x5556c4, 155%nat); (0x5559a8, 105%nat); (0x558120, 63%nat); (0x55f99c, 7%nat); (0x55fb94, 5%nat); (0x55fc24, 7%nat); (0x55fd2c, 33%nat); (0x561b2c, 11%nat); (0x56334c, 24%nat)].
Definition B_IT_003 : itab := mk_itab_ranges B_SEGS B_ranges_003.
Lemma B_IT_003_ok : itab_sound B_SEGS B_IT_003.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition B_shape_003 : shape := SHole 0.

Lemma B_cert_003 :
  check B_SEGS B_IT_003 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HS_003) 0%nat 400000%nat 40000%nat None B_HS_002 B_plan_003
  = COk B_shape_003.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_003)). Qed.
