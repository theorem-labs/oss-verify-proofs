(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs B_HS_010 B_HS_011.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition B_plan_011 : plan := PRun [0x1bf560] (PDiamondT 0x1bf78c 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PRun [0x1edb44] (PGcKeep [(escale 4096 (EVar 25), ELit 0); (escale 4096 (EVar 15), ELit 0); (ELit 0, ELit 5660672); (ELit 5664456, ELit 295); (ELit 6145704, ELit 623); (ELit 6148928, ELit 527); (ELit 6151608, ELit 471); (ELit 6153992, ELit 423); (ELit 6158272, ELit 879); (ELit 6168872, ELit 319); (ELit 6171688, ELit 758407); (ELit 6930176, ELit 495); (ELit 6933112, ELit 511); (ELit 6941468, ELit 267); (ELit 6943416, ELit 267); (ELit 6946712, ELit 295); (ELit 7476514, ELit 256); (ELit 7531848, ELit 287); (ELit 7540096, ELit 620); (ELit 7541088, ELit 256); (ELit 7803272, ELit 283); (ELit 9007720, ELit 4); (ELit 9241720, ELit 4); (ELit 12063256, ELit 151); (ELit 12327184, ELit 67344); (ELit 12394560, ELit 336); (ELit 12412416, ELit 132099); (ELit 12545384, ELit 263); (ELit 12547672, ELit 8); (ELit 12548632, ELit 263); (ELit 12550144, ELit 4611686018427387904)] (PGcRangeAuto (PCompact (PHandoff 0)))))))).
Definition B_ranges_011 : list (Z * nat) := [(0x194a14, 34%nat); (0x1a4b5c, 81%nat); (0x1a548c, 10%nat); (0x1a5ba8, 41%nat); (0x1a5cb0, 110%nat); (0x1a6088, 17%nat); (0x1bf500, 27%nat); (0x1bf730, 9%nat); (0x1bf784, 14%nat); (0x1bf868, 18%nat); (0x1d9c4c, 12%nat); (0x1d9cac, 5%nat); (0x1edb3c, 5%nat); (0x1ee020, 7%nat); (0x552f7c, 13%nat); (0x553034, 8%nat); (0x55f008, 66%nat)].
Definition B_IT_011 : itab := mk_itab_ranges B_SEGS B_ranges_011.
Lemma B_IT_011_ok : itab_sound B_SEGS B_IT_011.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition B_shape_011 : shape := SHole 0.

Lemma B_cert_011 :
  check B_SEGS B_IT_011 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HS_011) 0%nat 400000%nat 40000%nat None B_HS_010 B_plan_011
  = COk B_shape_011.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_011)). Qed.
