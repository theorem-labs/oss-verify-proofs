(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs B_HS_000 B_HS_001.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition B_plan_001 : plan := PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 283)) (ELit 4096) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar 283)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XMemIsZero [] (PRun [] (PX XMemset [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 348)) (ELit 4096) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar 348)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar 349)) (ELit 4096) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar 349)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PSys YMunmap (PSplit (EVar 6) 10 (PRun [0x1d9d98] (PFresh 10 12 (Some e_pgsp) (PRun [0x1bf560] (PDiamondT 0x1bf78c 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PFact (KWr (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PFact (KZero (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PX XMemset [] (PFact (KRange (esub (eaddz (escale 16 (EVar 6)) 3935) (escale 4096 (EVar 382))) 0 4095) (PFact (KRange (EVar 382) 0 1) (PHandoff 0))))))))))) (PRun [0x1d9d98] (PFresh 10 12 (Some e_pgsp) (PRun [0x1bf560] (PDiamondT 0x1bf78c 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PFact (KWr (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PFact (KZero (SA (eadd (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 10))) (escale 512 (EVar 382))) 2146402304) (ELit 1048576)) (PX XMemset [] (PFact (KRange (esub (eaddz (escale 16 (EVar 6)) 3935) (escale 4096 (EVar 382))) 0 4095) (PFact (KRange (EVar 382) 0 1) (PHandoff 0))))))))))))))))))))))))))))))))))))).
Definition B_ranges_001 : list (Z * nat) := [(0x1970a8, 29%nat); (0x1971cc, 10%nat); (0x1972d8, 23%nat); (0x1982b8, 24%nat); (0x1983a8, 13%nat); (0x1a6894, 15%nat); (0x1a75a4, 5%nat); (0x1aece4, 35%nat); (0x1bc8c8, 5%nat); (0x1bd31c, 55%nat); (0x1bd4c0, 29%nat); (0x1bf500, 43%nat); (0x1bf660, 9%nat); (0x1bf730, 39%nat); (0x1bf868, 18%nat); (0x1bf9fc, 31%nat); (0x1bfe88, 77%nat); (0x1bffec, 20%nat); (0x1c066c, 29%nat); (0x1c57c8, 17%nat); (0x1c7a2c, 7%nat); (0x1c7da4, 15%nat); (0x1c8074, 26%nat); (0x1c8518, 86%nat); (0x1c871c, 22%nat); (0x1c8820, 6%nat); (0x1c890c, 63%nat); (0x1c8b6c, 15%nat); (0x1c8c4c, 28%nat); (0x1c9eac, 78%nat); (0x1ca744, 16%nat); (0x1cc520, 30%nat); (0x1cfdc0, 13%nat); (0x1d036c, 43%nat); (0x1d0700, 18%nat); (0x1d1e04, 60%nat); (0x1d1f84, 30%nat); (0x1d2ae0, 21%nat); (0x1d2c30, 14%nat); (0x1d59fc, 30%nat); (0x1d5acc, 75%nat); (0x1d5c94, 38%nat); (0x1d5db8, 33%nat); (0x1d751c, 21%nat); (0x1d772c, 134%nat); (0x1d79dc, 13%nat); (0x1d8624, 50%nat); (0x1d9d00, 44%nat); (0x1d9e1c, 12%nat); (0x1da000, 36%nat); (0x1da274, 65%nat); (0x1da3f4, 56%nat); (0x1dab80, 117%nat); (0x553b40, 111%nat); (0x55f008, 66%nat); (0x55fcc0, 13%nat); (0x561b2c, 11%nat); (0x562c78, 17%nat)].
Definition B_IT_001 : itab := mk_itab_ranges B_SEGS B_ranges_001.
Lemma B_IT_001_ok : itab_sound B_SEGS B_IT_001.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition B_shape_001 : shape := SCase (EVar 6) 10 (SHole 0) (SHole 0).

Lemma B_cert_001 :
  check B_SEGS B_IT_001 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HS_001) 0%nat 400000%nat 40000%nat None B_HS_000 B_plan_001
  = COk B_shape_001.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_001)). Qed.
