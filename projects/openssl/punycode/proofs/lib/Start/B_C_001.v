(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs B_HS_000 B_HS_001.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition B_plan_001 : plan := PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 283)) (ELit 4096) (ELit 65536) (ELit 12505088) (PShDisj (escale 4096 (EVar 283)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XMemIsZero [] (PRun [] (PX XMemset [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 348)) (ELit 4096) (ELit 65536) (ELit 12505088) (PShDisj (escale 4096 (EVar 348)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 349)) (ELit 4096) (ELit 65536) (ELit 12505088) (PShDisj (escale 4096 (EVar 349)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PSys YMunmap (PSplit (EVar 6) 10 (PRun [0x1d9d4c] (PFresh 10 12 (Some e_pgsp) (PRun [0x1bf514] (PDiamondT 0x1bf740 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PFact (KWr (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PFact (KZero (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PX XMemset [] (PFact (KRange (esub (eaddz (escale 16 (EVar 6)) 3935) (escale 4096 (EVar 382))) 0 4095) (PFact (KRange (EVar 382) 0 1) (PHandoff 0))))))))))) (PRun [0x1d9d4c] (PFresh 10 12 (Some e_pgsp) (PRun [0x1bf514] (PDiamondT 0x1bf740 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PFact (KWr (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PFact (KZero (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PX XMemset [] (PFact (KRange (esub (eaddz (escale 16 (EVar 6)) 3935) (escale 4096 (EVar 382))) 0 4095) (PFact (KRange (EVar 382) 0 1) (PHandoff 0))))))))))))))))))))))))))))))))))))).
Definition B_ranges_001 : list (Z * nat) := [(0x19705c, 29%nat); (0x197180, 10%nat); (0x19728c, 23%nat); (0x19826c, 24%nat); (0x19835c, 13%nat); (0x1a6848, 15%nat); (0x1a7558, 5%nat); (0x1aec98, 35%nat); (0x1bc87c, 5%nat); (0x1bd2d0, 55%nat); (0x1bd474, 29%nat); (0x1bf4b4, 43%nat); (0x1bf614, 9%nat); (0x1bf6e4, 39%nat); (0x1bf81c, 18%nat); (0x1bf9b0, 31%nat); (0x1bfe3c, 77%nat); (0x1bffa0, 20%nat); (0x1c0620, 29%nat); (0x1c577c, 17%nat); (0x1c79e0, 7%nat); (0x1c7d58, 15%nat); (0x1c8028, 26%nat); (0x1c84cc, 86%nat); (0x1c86d0, 22%nat); (0x1c87d4, 6%nat); (0x1c88c0, 63%nat); (0x1c8b20, 15%nat); (0x1c8c00, 28%nat); (0x1c9e60, 78%nat); (0x1ca6f8, 16%nat); (0x1cc4d4, 30%nat); (0x1cfd74, 13%nat); (0x1d0320, 43%nat); (0x1d06b4, 18%nat); (0x1d1db8, 60%nat); (0x1d1f38, 30%nat); (0x1d2a94, 21%nat); (0x1d2be4, 14%nat); (0x1d59b0, 30%nat); (0x1d5a80, 75%nat); (0x1d5c48, 38%nat); (0x1d5d6c, 33%nat); (0x1d74d0, 21%nat); (0x1d76e0, 134%nat); (0x1d7990, 13%nat); (0x1d85d8, 50%nat); (0x1d9cb4, 44%nat); (0x1d9dd0, 12%nat); (0x1d9fb4, 36%nat); (0x1da228, 65%nat); (0x1da3a8, 56%nat); (0x1dab34, 117%nat); (0x558268, 111%nat); (0x563730, 66%nat); (0x5643e8, 13%nat); (0x566254, 11%nat); (0x5673a0, 17%nat)].
Definition B_IT_001 : itab := mk_itab_ranges B_SEGS B_ranges_001.
Lemma B_IT_001_ok : itab_sound B_SEGS B_IT_001.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition B_shape_001 : shape := SCase (EVar 6) 10 (SHole 0) (SHole 0).

Lemma B_cert_001 :
  check B_SEGS B_IT_001 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HS_001) 0%nat 400000%nat 40000%nat None B_HS_000 B_plan_001
  = COk B_shape_001.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_001)). Qed.
