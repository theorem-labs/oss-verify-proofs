(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_HS_002 A_HS_003.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition A_plan_003 : plan := PRun [] (PX XIMemset [] (PRun [] (PX XIMemset [] (PCase2 (esub (eaddz (escale 16 (EVar 6)) 3935) (escale 4096 (EVar 382))) 4030 (PRun [0x1a9248] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (ELit 65536) (ELit 12296192) (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (ELit 65536) (ELit 12296192) (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (ELit 65536) (ELit 12296192) (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [0x1a9548] (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 28; 29; 30; 31]%nat (PJoin (ELit 0) 9873216 4%nat (PJoin (ELit 0) 10946564 4%nat (PJoin (escale 4096 (EVar 491)) 16 8%nat (PHandoff 0))))))))))))))))))))))))) (PRun [0x1a9248] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (ELit 65536) (ELit 12296192) (PShDisj (escale 4096 (EVar 490)) (ELit 1048576) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (ELit 65536) (ELit 12296192) (PShDisj (escale 4096 (EVar 491)) (ELit 8388608) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (ELit 65536) (ELit 12296192) (PShDisj (escale 4096 (EVar 508)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [0x1a9548] (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 28; 29; 30; 31]%nat (PJoin (ELit 0) 9873216 4%nat (PJoin (ELit 0) 10946564 4%nat (PJoin (escale 4096 (EVar 491)) 16 8%nat (PHandoff 0))))))))))))))))))))))))))))).
Definition A_ranges_003 : list (Z * nat) := [(0x1a9110, 112%nat); (0x1a933c, 53%nat); (0x1a9490, 49%nat); (0x1aa4f8, 18%nat); (0x1ac4a4, 55%nat); (0x1c5710, 11%nat); (0x1c995c, 10%nat); (0x1ca5e8, 11%nat); (0x1ca7d0, 19%nat); (0x1cab4c, 13%nat); (0x1cb5f4, 50%nat); (0x1cb71c, 18%nat); (0x1cc518, 35%nat); (0x1cd118, 12%nat); (0x1cd2dc, 48%nat); (0x1cf724, 26%nat); (0x1cf7f0, 14%nat); (0x1d15c4, 15%nat); (0x1d1cd4, 5%nat); (0x1d1d1c, 5%nat); (0x1d4e64, 13%nat); (0x1d4ee0, 28%nat); (0x1d4f94, 17%nat); (0x1d5034, 11%nat); (0x1d57a4, 15%nat); (0x1d6ea8, 60%nat); (0x1d7028, 30%nat); (0x1d73e0, 58%nat); (0x1d7b84, 21%nat); (0x1d7cd4, 14%nat); (0x1d9f44, 36%nat); (0x1da180, 11%nat); (0x1da1dc, 68%nat); (0x1da42c, 19%nat); (0x1e2a44, 107%nat); (0x1e2c74, 7%nat); (0x1e3550, 42%nat); (0x1e4d58, 22%nat); (0x1e5040, 85%nat); (0x1e51d8, 71%nat); (0x1e57d4, 91%nat); (0x1e59c4, 29%nat); (0x1e5a6c, 37%nat); (0x1e6028, 35%nat); (0x1e6108, 18%nat); (0x1f293c, 79%nat); (0x1f30a4, 12%nat); (0x51f388, 18%nat); (0x5203d8, 21%nat); (0x520480, 27%nat); (0x520548, 17%nat); (0x5205f4, 40%nat); (0x5209c4, 53%nat); (0x520c04, 162%nat); (0x520fa0, 155%nat); (0x521284, 105%nat); (0x5239fc, 63%nat); (0x52b278, 7%nat); (0x52b470, 5%nat); (0x52b500, 7%nat); (0x52b608, 33%nat); (0x52d408, 11%nat); (0x52ec28, 24%nat)].
Definition A_IT_003 : itab := mk_itab_ranges A_SEGS A_ranges_003.
Lemma A_IT_003_ok : itab_sound A_SEGS A_IT_003.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition A_shape_003 : shape := SHole 0.

Lemma A_cert_003 :
  check A_SEGS A_IT_003 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HS_003) 0%nat 400000%nat 40000%nat None A_HS_002 A_plan_003
  = COk A_shape_003.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_003)). Qed.
