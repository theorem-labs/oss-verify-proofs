(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs B_HS_004 B_HS_005.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition B_plan_005 : plan := PBump 129 (PBump 153 (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 28; 29; 30; 31]%nat (PRename [(153, 97); (154, 98); (155, 99); (156, 100); (157, 101); (158, 102); (159, 103); (160, 104); (161, 105); (162, 106); (163, 107); (164, 108); (165, 109); (166, 110); (167, 111); (168, 112); (169, 113)]%nat (PGcKeep [(ELit 65536, ELit 12347936); (ELit 12428438, ELit 142186); (ELit 2147446784, ELit 41648); (ELit 2147550680, ELit 4); (ELit 2147550684, ELit 4); (ELit 2147591844, ELit 8); (ELit 2148994008, ELit 8264); (ELit 2149021472, ELit 136); (ELit 2147511452, ELit 268370788); (escale 4096 (EVar 31), ELit 0)] (PGcRangeAuto (PRun [] (PX XMemset [] (PRun [] (PBump 169 (PMmap PSpin (PRename [(169, 65)]%nat (PBand 0 (PShDisj (escale 4096 (EVar 35)) (ELit 11571200) (escale 4096 (EVar 65)) (ELit 65536) (PShDisj (escale 4096 (EVar 65)) (ELit 65536) (ELit 65536) (ELit 12505088) (PShDisj (escale 4096 (EVar 65)) (ELit 65536) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1bf514] (PDiamondT 0x1bf740 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PRun [0x1a4458] (PGcKeep [(ELit 65536, ELit 12347936); (ELit 12428438, ELit 142186); (ELit 2147446784, ELit 41648); (ELit 2147550680, ELit 4); (ELit 2147550684, ELit 4); (ELit 2147591844, ELit 8); (ELit 2148994008, ELit 8264); (ELit 2149021472, ELit 136); (ELit 2147511460, ELit 268370780); (escale 4096 (EVar 65), ELit 0)] (PGcRangeAuto (PCompact (PHandoff 0)))))))))))) (PShDisj (escale 4096 (EVar 35)) (ELit 11571200) (escale 4096 (EVar 65)) (ELit 65536) (PShDisj (escale 4096 (EVar 65)) (ELit 65536) (ELit 65536) (ELit 12505088) (PShDisj (escale 4096 (EVar 65)) (ELit 65536) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1bf514] (PDiamondT 0x1bf740 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PRun [0x1a4458] (PGcKeep [(ELit 65536, ELit 12347936); (ELit 12428438, ELit 142186); (ELit 2147446784, ELit 41648); (ELit 2147550680, ELit 4); (ELit 2147550684, ELit 4); (ELit 2147591844, ELit 8); (ELit 2148994008, ELit 8264); (ELit 2149021472, ELit 136); (ELit 2147511460, ELit 268370780); (escale 4096 (EVar 65), ELit 0)] (PGcRangeAuto (PCompact (PHandoff 0)))))))))))))))))))))))).
Definition B_ranges_005 : list (Z * nat) := [(0x1a443c, 30%nat); (0x1a4588, 6%nat); (0x1a46b4, 13%nat); (0x1a47e8, 63%nat); (0x1a49cc, 35%nat); (0x1a4ad8, 19%nat); (0x1a60d4, 90%nat); (0x1a6274, 116%nat); (0x1a64f4, 54%nat); (0x1a663c, 108%nat); (0x1a6998, 72%nat); (0x1bf4a0, 48%nat); (0x1bf614, 9%nat); (0x1bf6e4, 35%nat); (0x1bf81c, 18%nat); (0x1c486c, 10%nat); (0x1c5c58, 6%nat); (0x1ca634, 74%nat); (0x1cc4d4, 30%nat); (0x1d06b4, 18%nat); (0x1d1db8, 60%nat); (0x1d1f38, 30%nat); (0x1d2a94, 21%nat); (0x1d2be4, 14%nat); (0x563730, 66%nat)].
Definition B_IT_005 : itab := mk_itab_ranges B_SEGS B_ranges_005.
Lemma B_IT_005_ok : itab_sound B_SEGS B_IT_005.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition B_shape_005 : shape := SHole 0.

Lemma B_cert_005 :
  check B_SEGS B_IT_005 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HS_005) 0%nat 1500%nat 40000%nat None B_HS_004 B_plan_005
  = COk B_shape_005.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_005)). Qed.
