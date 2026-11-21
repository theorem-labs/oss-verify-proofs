(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.AS Require Import AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup2_plan_both_r0_1 : plan :=
  PRun [0x4a454]
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
  (PRun [0x8c4a8]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 1 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan_both_r1_2 : plan :=
  PRun [0x4a454]
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
  (PRun [0x8c4a8]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 2 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan_both : plan :=
  PBump 453
  (PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030
  (startup2_plan_both_r0_1)
  (startup2_plan_both_r1_2)).

Definition startup2_plan_both_ranges : list (Z * nat) := [(0x3bf50, 24%nat); (0x3bfc0, 4%nat); (0x4a320, 40%nat); (0x4a3f0, 60%nat); (0x4a550, 52%nat); (0x4a6a0, 36%nat); (0x4a740, 12%nat); (0x4a780, 12%nat); (0x4a880, 8%nat); (0x4a9b0, 12%nat); (0x4ab60, 32%nat); (0x4acd0, 32%nat); (0x4ae10, 36%nat); (0x4aeb0, 16%nat); (0x4af00, 20%nat); (0x4b700, 24%nat); (0x4be60, 40%nat); (0x4bf60, 32%nat); (0x4c000, 16%nat); (0x4c070, 20%nat); (0x4c0d0, 16%nat); (0x4c340, 16%nat); (0x4d6b0, 56%nat); (0x5fa20, 32%nat); (0x5fc60, 8%nat); (0x5fcb0, 16%nat); (0x5fda0, 16%nat); (0x60ba0, 8%nat); (0x64b90, 8%nat); (0x65da0, 4%nat); (0x66820, 52%nat); (0x66950, 16%nat); (0x682a0, 12%nat); (0x68460, 8%nat); (0x684a0, 12%nat); (0x68500, 8%nat); (0x6a660, 24%nat); (0x6a730, 12%nat); (0x6c500, 12%nat); (0x6fda0, 12%nat); (0x70600, 12%nat); (0x71cf0, 56%nat); (0x71e70, 8%nat); (0x71ec0, 8%nat); (0x72220, 56%nat); (0x729c0, 20%nat); (0x72b10, 16%nat); (0x78680, 12%nat); (0x786e0, 4%nat); (0x7c360, 68%nat); (0x7c490, 32%nat); (0x7c590, 8%nat); (0x7ce70, 40%nat); (0x7e680, 20%nat); (0x7e960, 84%nat); (0x7eb00, 4%nat); (0x7eb30, 44%nat); (0x7ec00, 4%nat); (0x7f0f0, 28%nat); (0x7f170, 60%nat); (0x7f2e0, 28%nat); (0x7f390, 20%nat); (0x7f3f0, 12%nat); (0x7f950, 20%nat); (0x7f9c0, 4%nat); (0x7fa30, 16%nat); (0x8c4a0, 4%nat); (0x8caf0, 12%nat); (0xbd460, 16%nat); (0xbd510, 12%nat); (0xc7a64, 68%nat); (0xc9304, 12%nat)]%Z.
