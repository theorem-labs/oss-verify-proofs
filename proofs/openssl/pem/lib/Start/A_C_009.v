(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_HS_008 A_HS_009.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition A_plan_009 : plan := PBump 133 (PExt 64 [escale 4096 (EVar 32)] (PBump 157 (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 28; 29; 30; 31]%nat (PRename [(157, 101); (158, 102); (159, 103); (160, 104); (161, 105); (162, 106); (163, 107); (164, 108); (165, 109); (166, 110); (167, 111); (168, 112); (169, 113); (170, 114); (171, 115); (172, 116); (173, 117)]%nat (PGcKeep [(ELit 65536, ELit 12122784); (ELit 12203373, ELit 141971); (ELit 2147446784, ELit 41492); (ELit 2147446784, ELit 268435456); (ELit 2147595320, ELit 8); (ELit 2148965872, ELit 8264); (ELit 2148993344, ELit 136); (ELit 2148145468, ELit 267736772); (escale 4096 (EVar 31), ELit 0)] (PGcRangeAuto (PRun [] (PBump 173 (PMmap PSpin (PRename [(173, 69)]%nat (PBand 0 (PShDisj (escale 4096 (EVar 32)) (ELit 8192) (escale 4096 (EVar 69)) (ELit 65536) (PShDisj (escale 4096 (EVar 41)) (ELit 11571200) (escale 4096 (EVar 69)) (ELit 65536) (PShDisj (escale 4096 (EVar 69)) (ELit 65536) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar 69)) (ELit 65536) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1c45a8] (PDiamondT 0x1c47d4 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [0x1a94ec] (PGcKeep [(ELit 65536, ELit 12122784); (ELit 12203373, ELit 141971); (ELit 2147446784, ELit 41492); (ELit 2147446784, ELit 268435456); (ELit 2147595320, ELit 8); (ELit 2148965872, ELit 8264); (ELit 2148993344, ELit 136); (ELit 2148145516, ELit 267736724); (escale 4096 (EVar 69), ELit 0)] (PGcRangeAuto (PCompact (PHandoff 0))))))))))))))) (PShDisj (escale 4096 (EVar 32)) (ELit 8192) (escale 4096 (EVar 69)) (ELit 65536) (PShDisj (escale 4096 (EVar 41)) (ELit 11571200) (escale 4096 (EVar 69)) (ELit 65536) (PShDisj (escale 4096 (EVar 69)) (ELit 65536) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar 69)) (ELit 65536) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1c45a8] (PDiamondT 0x1c47d4 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [0x1a94ec] (PGcKeep [(ELit 65536, ELit 12122784); (ELit 12203373, ELit 141971); (ELit 2147446784, ELit 41492); (ELit 2147446784, ELit 268435456); (ELit 2147595320, ELit 8); (ELit 2148965872, ELit 8264); (ELit 2148993344, ELit 136); (ELit 2148145516, ELit 267736724); (escale 4096 (EVar 69), ELit 0)] (PGcRangeAuto (PCompact (PHandoff 0)))))))))))))))))))))))))).
Definition A_ranges_009 : list (Z * nat) := [(0x1a94d0, 30%nat); (0x1a961c, 6%nat); (0x1a9748, 13%nat); (0x1a987c, 63%nat); (0x1a9a60, 35%nat); (0x1a9b6c, 19%nat); (0x1ab168, 90%nat); (0x1ab308, 116%nat); (0x1ab588, 54%nat); (0x1ab6d0, 108%nat); (0x1aba2c, 72%nat); (0x1c4534, 48%nat); (0x1c46a8, 9%nat); (0x1c4778, 35%nat); (0x1c48b0, 18%nat); (0x1c9900, 10%nat); (0x1cacec, 6%nat); (0x1cf6c8, 74%nat); (0x1d1568, 30%nat); (0x1d5748, 18%nat); (0x1d6e4c, 60%nat); (0x1d6fcc, 30%nat); (0x1d7b28, 21%nat); (0x1d7c78, 14%nat); (0x52690c, 66%nat)].
Definition A_IT_009 : itab := mk_itab_ranges A_SEGS A_ranges_009.
Lemma A_IT_009_ok : itab_sound A_SEGS A_IT_009.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition A_shape_009 : shape := SHole 0.

Lemma A_cert_009 :
  check A_SEGS A_IT_009 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HS_009) 0%nat 1500%nat 40000%nat None A_HS_008 A_plan_009
  = COk A_shape_009.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_009)). Qed.
