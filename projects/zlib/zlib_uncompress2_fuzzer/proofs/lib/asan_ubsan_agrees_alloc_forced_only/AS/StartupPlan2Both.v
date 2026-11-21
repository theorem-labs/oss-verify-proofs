(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup2_plan_both_r0_1 : plan :=
  PRun [0x4a648]
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
  (PRun [0x8c69c]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 1 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan_both_r1_2 : plan :=
  PRun [0x4a648]
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
  (PRun [0x8c69c]
  (PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 2 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup2_plan_both : plan :=
  PBump 453
  (PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030
  (startup2_plan_both_r0_1)
  (startup2_plan_both_r1_2)).

Definition startup2_plan_both_ranges : list (Z * nat) := [(0x3bfb8, 36%nat); (0x4a508, 48%nat); (0x4a5d8, 64%nat); (0x4a738, 56%nat); (0x4a888, 72%nat); (0x4aa78, 8%nat); (0x4ab98, 16%nat); (0x4ad58, 32%nat); (0x4aeb8, 36%nat); (0x4aff8, 84%nat); (0x4b8f8, 24%nat); (0x4c048, 44%nat); (0x4c148, 60%nat); (0x4c258, 48%nat); (0x4c528, 20%nat); (0x4d898, 60%nat); (0x5fc08, 36%nat); (0x5fe48, 12%nat); (0x5fea8, 16%nat); (0x5ff88, 20%nat); (0x60d88, 12%nat); (0x64d78, 12%nat); (0x65f88, 8%nat); (0x66a18, 52%nat); (0x66b38, 20%nat); (0x68488, 16%nat); (0x68648, 12%nat); (0x68688, 16%nat); (0x686e8, 12%nat); (0x6a848, 28%nat); (0x6a918, 16%nat); (0x6c6e8, 20%nat); (0x6ff88, 16%nat); (0x707e8, 16%nat); (0x71ed8, 64%nat); (0x72058, 12%nat); (0x720a8, 12%nat); (0x72408, 64%nat); (0x72bb8, 24%nat); (0x72d08, 16%nat); (0x78868, 16%nat); (0x788c8, 8%nat); (0x7c558, 68%nat); (0x7c678, 36%nat); (0x7c788, 8%nat); (0x7d058, 48%nat); (0x7e868, 24%nat); (0x7eb48, 88%nat); (0x7ece8, 72%nat); (0x7f2e8, 92%nat); (0x7f4d8, 32%nat); (0x7f578, 40%nat); (0x7fb38, 24%nat); (0x7fba8, 8%nat); (0x7fc18, 20%nat); (0x8c688, 8%nat); (0x8cd38, 16%nat); (0xbd6f8, 16%nat); (0xbd7b8, 12%nat); (0xc7cfc, 72%nat); (0xc95ac, 12%nat)]%Z.
