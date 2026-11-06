(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs B_HS_003 B_HS_004.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition B_plan_004 : plan := PBump 622 (PDropRange (ELit 2147488432) (ELit 103412) (PDropRange (ELit 2147591852) (ELit 1402156) (PDropRange (ELit 2149002272) (ELit 19200) (PDropRange (ELit 2149021608) (ELit 600) (PRun [] (PX XMemset [] (PRun [0x1a4458] (PExt 66 [ELit 2851] (PGcKeep [(ELit 65536, ELit 12347936); (ELit 12428438, ELit 142186); (ELit 2147446784, ELit 41648); (ELit 2147550680, ELit 4); (ELit 2147550684, ELit 4); (ELit 2147591844, ELit 8); (ELit 2148994008, ELit 8264); (ELit 2149021472, ELit 136); (ELit 2147511452, ELit 268370788); (escale 4096 (EVar 100), ELit 0)] (PGcRangeAuto (PCompact (PHandoff 0)))))))))))).
Definition B_ranges_004 : list (Z * nat) := [(0x1a443c, 30%nat); (0x1a4588, 6%nat); (0x1a46b4, 13%nat); (0x1a47e8, 63%nat); (0x1a49cc, 35%nat); (0x1a4ad8, 19%nat); (0x1a60d4, 90%nat); (0x1a6274, 116%nat); (0x1a64f4, 54%nat); (0x1a663c, 108%nat); (0x1a6998, 72%nat); (0x1bf4a0, 48%nat); (0x1bf614, 9%nat); (0x1bf6e4, 35%nat); (0x1bf81c, 18%nat); (0x1c486c, 10%nat); (0x1c5c58, 6%nat); (0x1ca634, 74%nat); (0x1cc4d4, 30%nat); (0x1d06b4, 18%nat); (0x1d1db8, 60%nat); (0x1d1f38, 30%nat); (0x1d2a94, 21%nat); (0x1d2be4, 14%nat); (0x563730, 66%nat)].
Definition B_IT_004 : itab := mk_itab_ranges B_SEGS B_ranges_004.
Lemma B_IT_004_ok : itab_sound B_SEGS B_IT_004.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition B_shape_004 : shape := SHole 0.

Lemma B_cert_004 :
  check B_SEGS B_IT_004 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HS_004) 0%nat 400000%nat 40000%nat None B_HS_003 B_plan_004
  = COk B_shape_004.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_004)). Qed.
