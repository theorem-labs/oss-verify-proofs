(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup2_plan_r0_1 : plan :=
  PRun [0x4a620]
  (PJoin e_sp0 (-2280) 8
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun [0x8c674]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 1 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan_r1_2 : plan :=
  PRun [0x4a620]
  (PJoin e_sp0 (-2280) 8
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun [0x8c674]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 2 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan : plan :=
  PBump 453
  (PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030
  (startup2_plan_r0_1)
  (startup2_plan_r1_2)).

Definition startup2_plan_ranges : list (Z * nat) := [(0x3bf90, 36%nat); (0x4a4e0, 48%nat); (0x4a5b0, 64%nat); (0x4a710, 56%nat); (0x4a860, 72%nat); (0x4aa50, 8%nat); (0x4ab70, 16%nat); (0x4ad30, 32%nat); (0x4ae90, 36%nat); (0x4afd0, 84%nat); (0x4b8d0, 24%nat); (0x4c020, 44%nat); (0x4c120, 60%nat); (0x4c230, 48%nat); (0x4c500, 20%nat); (0x4d870, 60%nat); (0x5fbe0, 36%nat); (0x5fe20, 12%nat); (0x5fe80, 16%nat); (0x5ff60, 20%nat); (0x60d60, 12%nat); (0x64d50, 12%nat); (0x65f60, 8%nat); (0x669f0, 52%nat); (0x66b10, 20%nat); (0x68460, 16%nat); (0x68620, 12%nat); (0x68660, 16%nat); (0x686c0, 12%nat); (0x6a820, 28%nat); (0x6a8f0, 16%nat); (0x6c6c0, 20%nat); (0x6ff60, 16%nat); (0x707c0, 16%nat); (0x71eb0, 64%nat); (0x72030, 12%nat); (0x72080, 12%nat); (0x723e0, 64%nat); (0x72b90, 24%nat); (0x72ce0, 16%nat); (0x78840, 16%nat); (0x788a0, 8%nat); (0x7c530, 68%nat); (0x7c650, 36%nat); (0x7c760, 8%nat); (0x7d030, 48%nat); (0x7e840, 24%nat); (0x7eb20, 88%nat); (0x7ecc0, 72%nat); (0x7f2c0, 92%nat); (0x7f4b0, 32%nat); (0x7f550, 40%nat); (0x7fb10, 24%nat); (0x7fb80, 8%nat); (0x7fbf0, 20%nat); (0x8c660, 8%nat); (0x8cdd0, 20%nat); (0xbc2b0, 16%nat); (0xbc370, 12%nat); (0xc68b4, 72%nat); (0xc8164, 12%nat)]%Z.
