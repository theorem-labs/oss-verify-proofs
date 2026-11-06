(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_HS_006 A_HS_007.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition A_plan_007 : plan := PBump 131 (PExt 64 [escale 4096 (EVar 32)] (PBump 155 (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 28; 29; 30; 31]%nat (PRename [(155, 99); (156, 100); (157, 101); (158, 102); (159, 103); (160, 104); (161, 105); (162, 106); (163, 107); (164, 108); (165, 109); (166, 110); (167, 111); (168, 112); (169, 113); (170, 114); (171, 115)]%nat (PGcKeep [(ELit 65536, ELit 12139232); (ELit 12219734, ELit 141994); (ELit 2147446784, ELit 41500); (ELit 2147553036, ELit 4); (ELit 2147553040, ELit 4); (ELit 2147595344, ELit 8); (ELit 2148967920, ELit 8264); (ELit 2148995384, ELit 136); (ELit 2147557920, ELit 268324320); (escale 4096 (EVar 31), ELit 0)] (PGcRangeAuto (PRun [] (PX XMemset [] (PRun [] (PBump 171 (PMmap PSpin (PRename [(171, 67)]%nat (PBand 0 (PShDisj (escale 4096 (EVar 32)) (ELit 4096) (escale 4096 (EVar 67)) (ELit 65536) (PShDisj (escale 4096 (EVar 36)) (ELit 11571200) (escale 4096 (EVar 67)) (ELit 65536) (PShDisj (escale 4096 (EVar 67)) (ELit 65536) (ELit 65536) (ELit 12296192) (PShDisj (escale 4096 (EVar 67)) (ELit 65536) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1c4604] (PDiamondT 0x1c4830 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PRun [0x1a9548] (PGcKeep [(ELit 65536, ELit 12139232); (ELit 12219734, ELit 141994); (ELit 2147446784, ELit 41500); (ELit 2147553036, ELit 4); (ELit 2147553040, ELit 4); (ELit 2147595344, ELit 8); (ELit 2148967920, ELit 8264); (ELit 2148995384, ELit 136); (ELit 2147557924, ELit 268324316); (escale 4096 (EVar 67), ELit 0)] (PGcRangeAuto (PCompact (PHandoff 0))))))))))))) (PShDisj (escale 4096 (EVar 32)) (ELit 4096) (escale 4096 (EVar 67)) (ELit 65536) (PShDisj (escale 4096 (EVar 36)) (ELit 11571200) (escale 4096 (EVar 67)) (ELit 65536) (PShDisj (escale 4096 (EVar 67)) (ELit 65536) (ELit 65536) (ELit 12296192) (PShDisj (escale 4096 (EVar 67)) (ELit 65536) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1c4604] (PDiamondT 0x1c4830 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PRun [0x1a9548] (PGcKeep [(ELit 65536, ELit 12139232); (ELit 12219734, ELit 141994); (ELit 2147446784, ELit 41500); (ELit 2147553036, ELit 4); (ELit 2147553040, ELit 4); (ELit 2147595344, ELit 8); (ELit 2148967920, ELit 8264); (ELit 2148995384, ELit 136); (ELit 2147557924, ELit 268324316); (escale 4096 (EVar 67), ELit 0)] (PGcRangeAuto (PCompact (PHandoff 0)))))))))))))))))))))))))).
Definition A_ranges_007 : list (Z * nat) := [(0x1a952c, 30%nat); (0x1a9678, 6%nat); (0x1a97a4, 13%nat); (0x1a98d8, 63%nat); (0x1a9abc, 35%nat); (0x1a9bc8, 19%nat); (0x1ab1c4, 90%nat); (0x1ab364, 116%nat); (0x1ab5e4, 54%nat); (0x1ab72c, 108%nat); (0x1aba88, 72%nat); (0x1c4590, 48%nat); (0x1c4704, 9%nat); (0x1c47d4, 35%nat); (0x1c490c, 18%nat); (0x1c995c, 10%nat); (0x1cad48, 6%nat); (0x1cf724, 74%nat); (0x1d15c4, 30%nat); (0x1d57a4, 18%nat); (0x1d6ea8, 60%nat); (0x1d7028, 30%nat); (0x1d7b84, 21%nat); (0x1d7cd4, 14%nat); (0x52a8e4, 66%nat)].
Definition A_IT_007 : itab := mk_itab_ranges A_SEGS A_ranges_007.
Lemma A_IT_007_ok : itab_sound A_SEGS A_IT_007.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition A_shape_007 : shape := SHole 0.

Lemma A_cert_007 :
  check A_SEGS A_IT_007 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HS_007) 0%nat 1500%nat 40000%nat None A_HS_006 A_plan_007
  = COk A_shape_007.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_007)). Qed.
