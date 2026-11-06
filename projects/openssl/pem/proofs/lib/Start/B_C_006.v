(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs B_HS_005 B_HS_006.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition B_plan_006 : plan := PBump 124 (PExt 66 [ELit 1065; ELit 1] (PRun [] (PBump 172 (PMmap PSpin (PRename [(172, 60)]%nat (PShDisj (escale 4096 (EVar 60)) (ELit 4096) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar 60)) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PExt 63 [escale 4096 (EVar 60)] (PRun [] (PX XMemset [] (PRun [0x1a44a4] (PExt 66 [ELit 2983; ELit 2] (PGcKeep [(ELit 65536, ELit 12329632); (ELit 12410221, ELit 139923); (ELit 2147446784, ELit 41636); (ELit 2147446784, ELit 268435456); (ELit 2147591840, ELit 8); (ELit 2148991728, ELit 8264); (ELit 2149019200, ELit 136); (ELit 2147557032, ELit 268325208); (escale 4096 (EVar 26), ELit 0)] (PGcRangeAuto (PCompact (PHandoff 0)))))))))))))))).
Definition B_ranges_006 : list (Z * nat) := [(0x1a4488, 30%nat); (0x1a45d4, 6%nat); (0x1a4700, 13%nat); (0x1a4834, 63%nat); (0x1a4a18, 35%nat); (0x1a4b24, 19%nat); (0x1a6120, 90%nat); (0x1a62c0, 116%nat); (0x1a6540, 54%nat); (0x1a6688, 108%nat); (0x1a69e4, 72%nat); (0x1bf4ec, 48%nat); (0x1bf660, 9%nat); (0x1bf730, 35%nat); (0x1bf868, 18%nat); (0x1c48b8, 10%nat); (0x1c5ca4, 6%nat); (0x1ca680, 74%nat); (0x1cc520, 30%nat); (0x1d0700, 18%nat); (0x1d1e04, 60%nat); (0x1d1f84, 30%nat); (0x1d2ae0, 21%nat); (0x1d2c30, 14%nat); (0x55f008, 66%nat)].
Definition B_IT_006 : itab := mk_itab_ranges B_SEGS B_ranges_006.
Lemma B_IT_006_ok : itab_sound B_SEGS B_IT_006.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition B_shape_006 : shape := SHole 0.

Lemma B_cert_006 :
  check B_SEGS B_IT_006 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HS_006) 0%nat 400000%nat 40000%nat None B_HS_005 B_plan_006
  = COk B_shape_006.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_006)). Qed.
