(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_HS_007 A_HS_008.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition A_plan_008 : plan := PBump 126 (PExt 64 [escale 4096 (EVar 28)] (PExt 66 [ELit 1362] (PRun [] (PBump 174 (PMmap PSpin (PRename [(174, 62)]%nat (PShDisj (escale 4096 (EVar 62)) (ELit 8192) (ELit 65536) (ELit 12296192) (PShDisj (escale 4096 (EVar 62)) (ELit 8192) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PExt 63 [escale 4096 (EVar 62)] (PRun [0x1aba90] (PExt 65 [] (PRun [] (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 62)) (ELit 8192) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 26)) (ELit 65536) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 15)) (ELit 65536) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 29)) (ELit 4096) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 30)) (ELit 8388608) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 31)) (ELit 1048576) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 27)) (ELit 11571200) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 32)) (ELit 4096) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 33)) (ELit 4096) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 34)) (ELit 65536) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 35)) (ELit 4096) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 37)) (ELit 137439023104) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 38)) (ELit 3727360) (PShDisj (escale 4096 (EVar 28)) (ELit 4096) (escale 4096 (EVar 39)) (ELit 65536) (PSys YMunmap (PRun [] (PX XMemset [] (PRun [0x1a9548] (PExt 66 [ELit 2431] (PExt 66 [ELit 161] (PGcKeep [(ELit 65536, ELit 12139232); (ELit 12219734, ELit 141994); (ELit 2147446784, ELit 41500); (ELit 2147553036, ELit 4); (ELit 2147553040, ELit 4); (ELit 2147595344, ELit 8); (ELit 2148967920, ELit 8264); (ELit 2148995384, ELit 136); (ELit 2148149692, ELit 267732548); (escale 4096 (EVar 26), ELit 0)] (PGcRangeAuto (PCompact (PHandoff 0)))))))))))))))))))))))))))))))))))).
Definition A_ranges_008 : list (Z * nat) := [(0x1a952c, 30%nat); (0x1a9678, 6%nat); (0x1a97a4, 13%nat); (0x1a98d8, 63%nat); (0x1a9abc, 35%nat); (0x1a9bc8, 19%nat); (0x1ab1c4, 90%nat); (0x1ab364, 116%nat); (0x1ab5e4, 54%nat); (0x1ab72c, 108%nat); (0x1aba88, 72%nat); (0x1c4590, 48%nat); (0x1c4704, 9%nat); (0x1c47d4, 35%nat); (0x1c490c, 18%nat); (0x1c995c, 10%nat); (0x1cad48, 6%nat); (0x1cf724, 74%nat); (0x1d15c4, 30%nat); (0x1d57a4, 18%nat); (0x1d6ea8, 60%nat); (0x1d7028, 30%nat); (0x1d7b84, 21%nat); (0x1d7cd4, 14%nat); (0x52a8e4, 66%nat)].
Definition A_IT_008 : itab := mk_itab_ranges A_SEGS A_ranges_008.
Lemma A_IT_008_ok : itab_sound A_SEGS A_IT_008.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition A_shape_008 : shape := SHole 0.

Lemma A_cert_008 :
  check A_SEGS A_IT_008 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HS_008) 0%nat 400000%nat 40000%nat None A_HS_007 A_plan_008
  = COk A_shape_008.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_008)). Qed.
