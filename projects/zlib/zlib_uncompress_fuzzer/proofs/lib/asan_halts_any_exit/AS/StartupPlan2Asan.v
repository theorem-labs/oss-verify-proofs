(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AS Require Import AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup2_plan_r0_1 : plan :=
  PRun [0x4a42c]
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
  (PRun [0x8c480]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 1 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan_r1_2 : plan :=
  PRun [0x4a42c]
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
  (PRun [0x8c480]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 2 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan : plan :=
  PBump 453
  (PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030
  (startup2_plan_r0_1)
  (startup2_plan_r1_2)).

Definition startup2_plan_ranges : list (Z * nat) := [(0x3bf30, 20%nat); (0x3bf90, 8%nat); (0x4a2f0, 44%nat); (0x4a3c0, 60%nat); (0x4a520, 52%nat); (0x4a670, 56%nat); (0x4a760, 8%nat); (0x4a860, 4%nat); (0x4a990, 8%nat); (0x4ab40, 28%nat); (0x4aca0, 36%nat); (0x4ade0, 36%nat); (0x4ae90, 12%nat); (0x4aed0, 20%nat); (0x4b6e0, 24%nat); (0x4be30, 40%nat); (0x4bf40, 32%nat); (0x4bfd0, 16%nat); (0x4c040, 44%nat); (0x4c310, 16%nat); (0x4d690, 52%nat); (0x5f9f0, 32%nat); (0x5fc40, 8%nat); (0x5fc90, 12%nat); (0x5fd70, 16%nat); (0x60b70, 8%nat); (0x64b60, 12%nat); (0x65d70, 4%nat); (0x66800, 48%nat); (0x66920, 20%nat); (0x68270, 12%nat); (0x68440, 4%nat); (0x68480, 12%nat); (0x684d0, 8%nat); (0x6a630, 28%nat); (0x6a700, 12%nat); (0x6c4d0, 8%nat); (0x6c500, 4%nat); (0x6fd70, 12%nat); (0x705d0, 16%nat); (0x71cc0, 60%nat); (0x71e40, 8%nat); (0x71e90, 8%nat); (0x72200, 56%nat); (0x729a0, 20%nat); (0x72af0, 12%nat); (0x78650, 12%nat); (0x786b0, 4%nat); (0x7c340, 68%nat); (0x7c460, 16%nat); (0x7c4b0, 12%nat); (0x7c570, 4%nat); (0x7ce50, 40%nat); (0x7e650, 20%nat); (0x7e940, 84%nat); (0x7ead0, 8%nat); (0x7eb10, 44%nat); (0x7ebd0, 8%nat); (0x7f0d0, 24%nat); (0x7f140, 60%nat); (0x7f2c0, 28%nat); (0x7f360, 36%nat); (0x7f920, 20%nat); (0x7f9a0, 4%nat); (0x7fa00, 16%nat); (0x8c480, 4%nat); (0x8cac0, 16%nat); (0xbbf50, 16%nat); (0xbc010, 12%nat); (0xc6554, 72%nat); (0xc7e04, 12%nat)]%Z.
