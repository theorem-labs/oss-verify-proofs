(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_HS_000 A_HS_001.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition A_plan_001 : plan := PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 283)) (ELit 4096) (ELit 65536) (ELit 12296192) (PShDisj (escale 4096 (EVar 283)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XMemIsZero [] (PRun [] (PX XMemset [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 348)) (ELit 4096) (ELit 65536) (ELit 12296192) (PShDisj (escale 4096 (EVar 348)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 349)) (ELit 4096) (ELit 65536) (ELit 12296192) (PShDisj (escale 4096 (EVar 349)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PSys YMunmap (PSplit (EVar 6) 10 (PRun [0x1dee3c] (PFresh 10 12 (Some e_pgsp) (PRun [0x1c4604] (PDiamondT 0x1c4830 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PFact (KWr (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PFact (KZero (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PX XMemset [] (PFact (KRange (esub (eaddz (escale 16 (EVar 6)) 3935) (escale 4096 (EVar 382))) 0 4095) (PFact (KRange (EVar 382) 0 1) (PHandoff 0))))))))))) (PRun [0x1dee3c] (PFresh 10 12 (Some e_pgsp) (PRun [0x1c4604] (PDiamondT 0x1c4830 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PFact (KWr (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PFact (KZero (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PX XMemset [] (PFact (KRange (esub (eaddz (escale 16 (EVar 6)) 3935) (escale 4096 (EVar 382))) 0 4095) (PFact (KRange (EVar 382) 0 1) (PHandoff 0))))))))))))))))))))))))))))))))))))).
Definition A_ranges_001 : list (Z * nat) := [(0x19c14c, 29%nat); (0x19c270, 10%nat); (0x19c37c, 23%nat); (0x19d35c, 24%nat); (0x19d44c, 13%nat); (0x1ab938, 15%nat); (0x1ac648, 5%nat); (0x1b3d88, 35%nat); (0x1c196c, 5%nat); (0x1c23c0, 55%nat); (0x1c2564, 29%nat); (0x1c45a4, 43%nat); (0x1c4704, 9%nat); (0x1c47d4, 39%nat); (0x1c490c, 18%nat); (0x1c4aa0, 31%nat); (0x1c4f2c, 77%nat); (0x1c5090, 20%nat); (0x1c5710, 29%nat); (0x1ca86c, 17%nat); (0x1ccad0, 7%nat); (0x1cce48, 15%nat); (0x1cd118, 26%nat); (0x1cd5bc, 86%nat); (0x1cd7c0, 22%nat); (0x1cd8c4, 6%nat); (0x1cd9b0, 63%nat); (0x1cdc10, 15%nat); (0x1cdcf0, 28%nat); (0x1cef50, 78%nat); (0x1cf7e8, 16%nat); (0x1d15c4, 30%nat); (0x1d4e64, 13%nat); (0x1d5410, 43%nat); (0x1d57a4, 18%nat); (0x1d6ea8, 60%nat); (0x1d7028, 30%nat); (0x1d7b84, 21%nat); (0x1d7cd4, 14%nat); (0x1daaa0, 30%nat); (0x1dab70, 75%nat); (0x1dad38, 38%nat); (0x1dae5c, 33%nat); (0x1dc5c0, 21%nat); (0x1dc7d0, 134%nat); (0x1dca80, 13%nat); (0x1dd6c8, 50%nat); (0x1deda4, 44%nat); (0x1deec0, 12%nat); (0x1df0a4, 36%nat); (0x1df318, 65%nat); (0x1df498, 56%nat); (0x1dfc24, 117%nat); (0x51f41c, 111%nat); (0x52a8e4, 66%nat); (0x52b59c, 13%nat); (0x52d408, 11%nat); (0x52e554, 17%nat)].
Definition A_IT_001 : itab := mk_itab_ranges A_SEGS A_ranges_001.
Lemma A_IT_001_ok : itab_sound A_SEGS A_IT_001.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition A_shape_001 : shape := SCase (EVar 6) 10 (SHole 0) (SHole 0).

Lemma A_cert_001 :
  check A_SEGS A_IT_001 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HS_001) 0%nat 400000%nat 40000%nat None A_HS_000 A_plan_001
  = COk A_shape_001.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_001)). Qed.
