(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_HS_010 A_HS_011.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition A_plan_011 : plan := PRun [0x1c4604] (PDiamondT 0x1c4830 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PRun [0x1f2be8] (PGcKeep [(escale 4096 (EVar 25), ELit 0); (escale 4096 (EVar 15), ELit 0); (ELit 0, ELit 5447680); (ELit 5449656, ELit 271); (ELit 5932040, ELit 623); (ELit 5935264, ELit 527); (ELit 5937952, ELit 471); (ELit 5940328, ELit 423); (ELit 5944608, ELit 879); (ELit 5955208, ELit 319); (ELit 5957320, ELit 782311); (ELit 6739712, ELit 495); (ELit 6742648, ELit 511); (ELit 6751004, ELit 267); (ELit 6752952, ELit 267); (ELit 6756248, ELit 295); (ELit 7286050, ELit 256); (ELit 7341384, ELit 287); (ELit 7349632, ELit 620); (ELit 7350624, ELit 256); (ELit 7612808, ELit 283); (ELit 9873216, ELit 4); (ELit 10946564, ELit 4); (ELit 11872792, ELit 151); (ELit 12136720, ELit 65840); (ELit 12203488, ELit 256); (ELit 12221920, ELit 132099); (ELit 12354888, ELit 263); (ELit 12358136, ELit 263); (ELit 12361728, ELit 4611686018427387904)] (PGcRangeAuto (PCompact (PHandoff 0)))))))).
Definition A_ranges_011 : list (Z * nat) := [(0x199ab8, 34%nat); (0x1a9c00, 81%nat); (0x1aa530, 10%nat); (0x1aac4c, 41%nat); (0x1aad54, 110%nat); (0x1ab12c, 17%nat); (0x1c45a4, 27%nat); (0x1c47d4, 9%nat); (0x1c4828, 14%nat); (0x1c490c, 18%nat); (0x1decf0, 12%nat); (0x1ded50, 5%nat); (0x1f2be0, 5%nat); (0x1f30c4, 7%nat); (0x51e858, 13%nat); (0x51e910, 8%nat); (0x52a8e4, 66%nat)].
Definition A_IT_011 : itab := mk_itab_ranges A_SEGS A_ranges_011.
Lemma A_IT_011_ok : itab_sound A_SEGS A_IT_011.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition A_shape_011 : shape := SHole 0.

Lemma A_cert_011 :
  check A_SEGS A_IT_011 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HS_011) 0%nat 400000%nat 40000%nat None A_HS_010 A_plan_011
  = COk A_shape_011.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_011)). Qed.
