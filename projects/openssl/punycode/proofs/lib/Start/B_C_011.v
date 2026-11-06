(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs B_HS_010 B_HS_011.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition B_plan_011 : plan := PRun [0x1bf514] (PDiamondT 0x1bf740 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PRun [0x1edaf8] (PGcKeep [(escale 4096 (EVar 25), ELit 0); (escale 4096 (EVar 15), ELit 0); (ELit 0, ELit 5681152); (ELit 5682688, ELit 271); (ELit 6163912, ELit 623); (ELit 6167136, ELit 527); (ELit 6169816, ELit 479); (ELit 6172208, ELit 423); (ELit 6176480, ELit 879); (ELit 6187080, ELit 319); (ELit 6189896, ELit 758439); (ELit 6948416, ELit 495); (ELit 6951352, ELit 511); (ELit 6959708, ELit 267); (ELit 6961656, ELit 267); (ELit 6964952, ELit 295); (ELit 7494754, ELit 256); (ELit 7550088, ELit 287); (ELit 7558336, ELit 620); (ELit 7559328, ELit 256); (ELit 7821512, ELit 283); (ELit 11663372, ELit 4); (ELit 7891516, ELit 4); (ELit 12081496, ELit 151); (ELit 12345424, ELit 65840); (ELit 12412192, ELit 256); (ELit 12430624, ELit 132099); (ELit 12563592, ELit 263); (ELit 12566840, ELit 263); (ELit 12570624, ELit 4611686018427387904)] (PGcRangeAuto (PCompact (PHandoff 0)))))))).
Definition B_ranges_011 : list (Z * nat) := [(0x1949c8, 34%nat); (0x1a4b10, 81%nat); (0x1a5440, 10%nat); (0x1a5b5c, 41%nat); (0x1a5c64, 110%nat); (0x1a603c, 17%nat); (0x1bf4b4, 27%nat); (0x1bf6e4, 9%nat); (0x1bf738, 14%nat); (0x1bf81c, 18%nat); (0x1d9c00, 12%nat); (0x1d9c60, 5%nat); (0x1edaf0, 5%nat); (0x1edfd4, 7%nat); (0x5576a4, 13%nat); (0x55775c, 8%nat); (0x563730, 66%nat)].
Definition B_IT_011 : itab := mk_itab_ranges B_SEGS B_ranges_011.
Lemma B_IT_011_ok : itab_sound B_SEGS B_IT_011.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition B_shape_011 : shape := SHole 0.

Lemma B_cert_011 :
  check B_SEGS B_IT_011 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HS_011) 0%nat 400000%nat 40000%nat None B_HS_010 B_plan_011
  = COk B_shape_011.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_011)). Qed.
